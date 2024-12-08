#include "ftl.h"

//#define FEMU_DEBUG_FTL

static int do_gc(struct ssd *ssd, uint16_t rgid, bool force, NvmeRequest *req);
static void *ftl_thread(void *arg);

static inline bool should_gc_high(struct ssd *ssd, uint16_t rg)
{
	return (ssd->rums[rg].free_ru_cnt <= ssd->sp.gc_thres_rus_high); 
}																

static inline struct ppa get_maptbl_ent(struct ssd *ssd, uint64_t lpn)
{
    return ssd->maptbl[lpn];
}

static inline void set_maptbl_ent(struct ssd *ssd, uint64_t lpn, struct ppa *ppa)
{
    ftl_assert(lpn < ssd->sp.tt_pgs);
    ssd->maptbl[lpn] = *ppa;
}

static uint64_t ppa2pgidx(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    uint64_t pgidx;

    pgidx = ppa->g.ch  * spp->pgs_per_ch  + \
            ppa->g.lun * spp->pgs_per_lun + \
            ppa->g.pl  * spp->pgs_per_pl  + \
            ppa->g.blk * spp->pgs_per_blk + \
            ppa->g.pg;

    ftl_assert(pgidx < spp->tt_pgs);

    return pgidx;
}

static inline uint64_t get_rmap_ent(struct ssd *ssd, struct ppa *ppa)
{
    uint64_t pgidx = ppa2pgidx(ssd, ppa);

    return ssd->rmap[pgidx];
}

/* set rmap[page_no(ppa)] -> lpn */
static inline void set_rmap_ent(struct ssd *ssd, uint64_t lpn, struct ppa *ppa)
{
    uint64_t pgidx = ppa2pgidx(ssd, ppa);

    ssd->rmap[pgidx] = lpn;
}

static inline int victim_line_cmp_pri(pqueue_pri_t next, pqueue_pri_t curr)
{
    return (next > curr);
}

static inline pqueue_pri_t victim_line_get_pri(void *a)
{
    return ((struct line *)a)->vpc;
}

static inline void victim_line_set_pri(void *a, pqueue_pri_t pri)
{
    ((struct line *)a)->vpc = pri;
}

static inline size_t victim_line_get_pos(void *a)
{
    return ((struct line *)a)->pos;
}

static inline void victim_line_set_pos(void *a, size_t pos)
{
    ((struct line *)a)->pos = pos;
}

static void ssd_init_lines(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;
    struct line_mgmt *lm = &ssd->lm;
    struct line *line;

    lm->tt_lines = spp->blks_per_pl;
    ftl_assert(lm->tt_lines == spp->tt_lines);
    lm->lines = g_malloc0(sizeof(struct line) * lm->tt_lines);

    QTAILQ_INIT(&lm->free_line_list);
    lm->victim_line_pq = pqueue_init(spp->tt_lines, victim_line_cmp_pri,
            victim_line_get_pri, victim_line_set_pri,
            victim_line_get_pos, victim_line_set_pos);
    QTAILQ_INIT(&lm->full_line_list);

    lm->free_line_cnt = 0;
    for (int i = 0; i < lm->tt_lines; i++) {
        line = &lm->lines[i];
        line->id = i;
        line->ipc = 0;
        line->vpc = 0;
        line->pos = 0;
        /* initialize all the lines as free lines */
        QTAILQ_INSERT_TAIL(&lm->free_line_list, line, entry);
        lm->free_line_cnt++;
    }

    ftl_assert(lm->free_line_cnt == lm->tt_lines);
    lm->victim_line_cnt = 0;
    lm->full_line_cnt = 0;
}

static inline int victim_ru_cmp_pri(pqueue_pri_t next, pqueue_pri_t curr)
{
    return (next > curr);
}

static inline pqueue_pri_t victim_ru_get_pri(void *a)		
{
    return ((struct ru *)a)->vpc;
}

static inline void victim_ru_set_pri(void *a, pqueue_pri_t pri)
{
    ((struct ru *)a)->vpc = pri;
}

static inline size_t victim_ru_get_pos(void *a)
{
    return ((struct ru *)a)->pos;
}

static inline void victim_ru_set_pos(void *a, size_t pos)
{
    ((struct ru *)a)->pos = pos;
}																		

static void ssd_init_fdp_ru_mgmts(struct ssd *ssd) 	
{
	struct ssdparams *spp = &ssd->sp;
    struct ru_mgmt *rum = NULL;
    struct ru *ru = NULL;
	int nrg = spp->tt_luns / RG_DEGREE;
	int blkoff;
	
	ssd->rums = g_malloc(sizeof(struct ru_mgmt) * nrg);
	for (int i = 0; i < nrg; i++) {
		rum = &ssd->rums[i];
		rum->tt_rus = spp->blks_per_lun;
		assert(rum->tt_rus == spp->blks_per_lun);
		rum->rus = g_malloc0(sizeof(struct ru) * rum->tt_rus);

		QTAILQ_INIT(&rum->free_ru_list);
		rum->victim_ru_pq = pqueue_init(spp->tt_blks, victim_ru_cmp_pri,
            victim_ru_get_pri, victim_ru_set_pri,
            victim_ru_get_pos, victim_ru_set_pos);
		QTAILQ_INIT(&rum->full_ru_list);

		rum->free_ru_cnt = 0;

		for (int j = 0; j < rum->tt_rus; j++) {
			ru = &rum->rus[j];
			ru->id = j;
			ru->wp.ch = i * RG_DEGREE / spp->luns_per_ch;
			ru->wp.lun = i * RG_DEGREE % spp->luns_per_ch; 
			ru->wp.pl = 0;
			ru->wp.blk = j;
			ru->wp.pg = 0;
			ru->ipc = 0;
			ru->vpc = 0;
			ru->pos = 0; 
			/* ruh history for gc */	
			if (j < MAX_RUHS)
				ru->ruhid = j;

			blkoff = j % spp->blks_per_pl;
			for (int k = 0; k < RG_DEGREE; k++) {
				int cur_ch = ru->wp.ch + k / spp->luns_per_ch;
				int cur_lun = (ru->wp.lun + k) % spp->luns_per_ch;

				ru->blks[k] = &ssd->ch[cur_ch].lun[cur_lun].pl[0].blk[blkoff]; 
			} 

			/* initialize all the reclaim units as free reclaim units */
			QTAILQ_INSERT_TAIL(&rum->free_ru_list, ru, entry);
			rum->free_ru_cnt++;
		}

		ftl_assert(rum->free_ru_cnt == rum->tt_rus);
		rum->victim_ru_cnt = 0;
		rum->full_ru_cnt = 0; 
	} 
}														

static int get_next_free_ruid(struct ssd *ssd, struct ru_mgmt *rum) 
{
	struct ru *retru = NULL;

	retru = QTAILQ_FIRST(&rum->free_ru_list);
	if (!retru) {
		ftl_err("No free reclaim units left in [%s] !!!!\n", ssd->ssdname);
		return -1;
	}
	QTAILQ_REMOVE(&rum->free_ru_list, retru, entry);
	rum->free_ru_cnt--;

	return retru->id; 
}																		

static void ssd_init_fdp_ruhtbl(struct FemuCtrl *n, struct ssd *ssd) 
{
	NvmeEnduranceGroup *endgrp = &n->endgrps[0];
	struct ruh *ruh = NULL;
	struct ru_mgmt *rum = NULL;

	ssd->fdp_enabled = endgrp->fdp.enabled;
	ssd->ruhtbl = g_malloc0(sizeof(struct ruh) * endgrp->fdp.nruh); 
	for (int i = 0; i < endgrp->fdp.nruh; i++) {
		ruh = &ssd->ruhtbl[i];
		ruh->ruht = endgrp->fdp.ruhs[i].ruht;
		ruh->cur_ruids = g_malloc0(sizeof(int) * endgrp->fdp.nrg);
		for (int j = 0; j < endgrp->fdp.nrg; j++)  {
			rum = &ssd->rums[j];
			ruh->cur_ruids[j] = get_next_free_ruid(ssd, rum);
		} 
	} 

	/* reserve one ru for initially isolated gc */
	for (int i = 0; i < endgrp->fdp.nrg; i++) {
		rum = &ssd->rums[i];
		rum->ii_gc_ruid = get_next_free_ruid(ssd, rum);
	}
}																		

static inline void check_addr(int a, int max)
{
    ftl_assert(a >= 0 && a < max);
}

static void ssd_advance_ru_write_pointer(struct ssd *ssd, uint16_t rgid, uint16_t ruhid, bool for_gc) 
{
	/* 3. Advancing Write Pointer */
	/*****************/

    struct ssdparams *spp = &ssd->sp;
    struct ru_mgmt *rum = &ssd->rums[rgid];
    struct ruh *ruh = &ssd->ruhtbl[ruhid];
    struct ru *ru = NULL;

    int cur_ruid = -1;
    if (for_gc)
    {

        cur_ruid = rum->ii_gc_ruid;
        ru = &rum->rus[cur_ruid];


        ru->wp.ch++;
        if (ru->wp.ch == (rgid+1) * RG_DEGREE / spp->luns_per_ch)
        {
            ru->wp.ch = 0;
            ru->wp.lun++;
            if (ru->wp.lun == spp->luns_per_ch)
            {
                ru->wp.lun = 0;
                ru->wp.pg++;
                // RU is full
                if (ru->wp.pg >= spp->pgs_per_ru)
                {
                    ru->wp.pg = 0;
                    // All pages are valid
                    if (ru->vpc == spp->pgs_per_ru)
                    {
                        // RU is full, move to full list
                        QTAILQ_INSERT_TAIL(&rum->full_ru_list, ru, entry);
                        rum->full_ru_cnt++;
                    }
                    else
                    {
                        // RU is partially used, insert into victim queue
                        pqueue_insert(rum->victim_ru_pq, ru);
                        rum->victim_ru_cnt++;
                    }

                    // Reset ii_gc_ruid
                    rum->ii_gc_ruid = -1;

                    // Get a new RU from free_ru_list
                    ru = QTAILQ_FIRST(&rum->free_ru_list);

                    // Remove RU from free list
                    QTAILQ_REMOVE(&rum->free_ru_list, ru, entry);
                    rum->free_ru_cnt--;

                    // Assign RU to GC RU
                    rum->ii_gc_ruid = ru->id;

                    // Initialize write pointer
                    int start_lunidx = rgid * RG_DEGREE;
                    ru->wp.ch = start_lunidx / spp->luns_per_ch;
                    ru->wp.lun = start_lunidx % spp->luns_per_ch;
                    ru->wp.pl = 0;
                    ru->wp.blk = ru->id;
                    ru->wp.pg = 0;

                    // Reset RU's counters
                    ru->vpc = 0;
                    ru->ipc = 0;
                }
            }
        }
    }
    else
    {
        // Normal operation
        cur_ruid = ruh->cur_ruids[rgid];
        ru = &rum->rus[cur_ruid];

        ru->wp.ch++;
        if (ru->wp.ch == spp->nchs) // 이게 맞나?
        {
            ru->wp.ch = 0;
            ru->wp.lun++;
            if (ru->wp.lun == spp->luns_per_ch)
            {
                ru->wp.lun = 0;
                ru->wp.pg++;
                // RU is full
                if (ru->wp.pg >= spp->pgs_per_ru)
                {
                    ru->wp.pg = 0;
                    // All pages are valid
                    if (ru->vpc == spp->pgs_per_ru)
                    {
                        // RU is full, move to full list
                        QTAILQ_INSERT_TAIL(&rum->full_ru_list, ru, entry);
                        rum->full_ru_cnt++;
                    }
                    else
                    {
                        // RU is partially used, insert into victim queue
                        pqueue_insert(rum->victim_ru_pq, ru);
                        rum->victim_ru_cnt++;
                    }

                    // Get a new RU from free_ru_list
                    ru = QTAILQ_FIRST(&rum->free_ru_list);

                    // Remove RU from free list
                    QTAILQ_REMOVE(&rum->free_ru_list, ru, entry);
                    rum->free_ru_cnt--;

                    // Initialize write pointer / 0, 2, 4, 6,
                    int start_lunidx = rgid * RG_DEGREE; // RG_DEGREE defined 16
                    ru->wp.ch = start_lunidx / spp->luns_per_ch;  // ~/8
                    ru->wp.lun = start_lunidx % spp->luns_per_ch;
                    ru->wp.pl = 0;
                    ru->wp.blk = ru->id;
                    ru->wp.pg = 0;

                    // Reset RU's counters
                    ru->vpc = 0;
                    ru->ipc = 0;
                }
            }
        }
    }

    /*****************/
}																

static struct ppa get_new_page(struct ssd *ssd, uint16_t rgid, uint16_t ruhid, bool for_gc) 
{
	/* 2. Getting Physical Page to Write */
	// /**************
    struct ppa ppa;

    // struct ssdparams *spp = &ssd->sp;
    struct ru_mgmt *rum = &ssd->rums[rgid];
    struct ru *ru = NULL;
    struct ruh *ruh = &ssd->ruhtbl[ruhid];

    int ruid = ruh->cur_ruids[rgid]; // offset value within RG

    if (for_gc) {
        // Use the GC RU for Initially Isolated data
        ruid = rum->ii_gc_ruid;
        ru = &rum->rus[ruid];

        // Construct the physical page address (PPA)
        ppa.g.ch = ru->wp.ch;
        ppa.g.lun = ru->wp.lun;
        ppa.g.pl = ru->wp.pl;
        ppa.g.blk = ru->wp.blk;
        ppa.g.pg = ru->wp.pg;
        ppa.g.sec = 0; // Assuming a full page write

        return ppa;
    }

    ru = &rum->rus[ruid];

    ppa.g.ch = ru->wp.ch;
    ppa.g.lun = ru->wp.lun;
    ppa.g.pg = ru->wp.pg;
    ppa.g.blk = ru->wp.blk;
    ppa.g.pl = ru->wp.pl;
    ftl_assert(ppa.g.pl == 0);

    return ppa;
	// **************/
}																		

static void ssd_init_params(struct ssdparams *spp, FemuCtrl *n)
{
    spp->secsz = n->bb_params.secsz; // 512
    spp->secs_per_pg = n->bb_params.secs_per_pg; // 8
    spp->pgs_per_blk = n->bb_params.pgs_per_blk; //256
    spp->blks_per_pl = n->bb_params.blks_per_pl; /* 256 16GB */
    spp->pls_per_lun = n->bb_params.pls_per_lun; // 1
    spp->luns_per_ch = n->bb_params.luns_per_ch; // 8
    spp->nchs = n->bb_params.nchs; // 8

    spp->pg_rd_lat = n->bb_params.pg_rd_lat;
    spp->pg_wr_lat = n->bb_params.pg_wr_lat;
    spp->blk_er_lat = n->bb_params.blk_er_lat;
    spp->ch_xfer_lat = n->bb_params.ch_xfer_lat;

    /* calculated values */
    spp->secs_per_blk = spp->secs_per_pg * spp->pgs_per_blk;
    spp->secs_per_pl = spp->secs_per_blk * spp->blks_per_pl;
    spp->secs_per_lun = spp->secs_per_pl * spp->pls_per_lun;
    spp->secs_per_ch = spp->secs_per_lun * spp->luns_per_ch;
    spp->tt_secs = spp->secs_per_ch * spp->nchs;

    spp->pgs_per_pl = spp->pgs_per_blk * spp->blks_per_pl;
    spp->pgs_per_lun = spp->pgs_per_pl * spp->pls_per_lun;
    spp->pgs_per_ch = spp->pgs_per_lun * spp->luns_per_ch;
    spp->tt_pgs = spp->pgs_per_ch * spp->nchs;

    spp->blks_per_lun = spp->blks_per_pl * spp->pls_per_lun;
    spp->blks_per_ch = spp->blks_per_lun * spp->luns_per_ch;
    spp->tt_blks = spp->blks_per_ch * spp->nchs;

    spp->pls_per_ch =  spp->pls_per_lun * spp->luns_per_ch;
    spp->tt_pls = spp->pls_per_ch * spp->nchs;

    spp->tt_luns = spp->luns_per_ch * spp->nchs;

    /* line is special, put it at the end */
    spp->blks_per_line = spp->tt_luns; /* TODO: to fix under multiplanes */
    spp->pgs_per_line = spp->blks_per_line * spp->pgs_per_blk;
    spp->secs_per_line = spp->pgs_per_line * spp->secs_per_pg;
    spp->tt_lines = spp->blks_per_lun; /* TODO: to fix under multiplanes */

    spp->blks_per_ru = RG_DEGREE; 									
    spp->pgs_per_ru = spp->blks_per_ru * spp->pgs_per_blk;
    spp->secs_per_ru = spp->pgs_per_ru * spp->secs_per_pg;
	spp->chs_per_ru = RG_DEGREE / spp->luns_per_ch;
	spp->luns_per_ru = spp->blks_per_ru;
    spp->tt_rus = spp->blks_per_lun;							
	
    spp->gc_thres_pcent = n->bb_params.gc_thres_pcent/100.0;
    spp->gc_thres_lines = (int)((1 - spp->gc_thres_pcent) * spp->tt_lines);
    spp->gc_thres_pcent_high = n->bb_params.gc_thres_pcent_high/100.0; 
    spp->gc_thres_lines_high = (int)((1 - spp->gc_thres_pcent_high) * spp->tt_lines);
    spp->gc_thres_rus_high = (int)((1 - spp->gc_thres_pcent_high) * spp->tt_rus); 
    spp->enable_gc_delay = true; 
}

static void ssd_init_nand_page(struct nand_page *pg, struct ssdparams *spp)
{
    pg->nsecs = spp->secs_per_pg;
    pg->sec = g_malloc0(sizeof(nand_sec_status_t) * pg->nsecs);
    for (int i = 0; i < pg->nsecs; i++) {
        pg->sec[i] = SEC_FREE;
    }
    pg->status = PG_FREE;
}

static void ssd_init_nand_blk(struct nand_block *blk, struct ssdparams *spp)
{
    blk->npgs = spp->pgs_per_blk;
    blk->pg = g_malloc0(sizeof(struct nand_page) * blk->npgs);
    for (int i = 0; i < blk->npgs; i++) {
        ssd_init_nand_page(&blk->pg[i], spp);
    }
    blk->ipc = 0;
    blk->vpc = 0;
    blk->erase_cnt = 0;
    blk->wp = 0;
}

static void ssd_init_nand_plane(struct nand_plane *pl, struct ssdparams *spp)
{
    pl->nblks = spp->blks_per_pl;
    pl->blk = g_malloc0(sizeof(struct nand_block) * pl->nblks);
    for (int i = 0; i < pl->nblks; i++) {
        ssd_init_nand_blk(&pl->blk[i], spp);
    }
}

static void ssd_init_nand_lun(struct nand_lun *lun, struct ssdparams *spp)
{
    lun->npls = spp->pls_per_lun;
    lun->pl = g_malloc0(sizeof(struct nand_plane) * lun->npls);
    for (int i = 0; i < lun->npls; i++) {
        ssd_init_nand_plane(&lun->pl[i], spp);
    }
    lun->next_lun_avail_time = 0;
    lun->busy = false;
}

static void ssd_init_ch(struct ssd_channel *ch, struct ssdparams *spp)
{
    ch->nluns = spp->luns_per_ch;
    ch->lun = g_malloc0(sizeof(struct nand_lun) * ch->nluns);
    for (int i = 0; i < ch->nluns; i++) {
        ssd_init_nand_lun(&ch->lun[i], spp);
    }
    ch->next_ch_avail_time = 0;
    ch->busy = 0;
}

static void ssd_init_maptbl(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->maptbl = g_malloc0(sizeof(struct ppa) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++) {
        ssd->maptbl[i].ppa = UNMAPPED_PPA;
    }
}

static void ssd_init_rmap(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->rmap = g_malloc0(sizeof(uint64_t) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++) {
        ssd->rmap[i] = INVALID_LPN;
    }
}

void ssd_init(FemuCtrl *n)
{
    struct ssd *ssd = n->ssd;
    struct ssdparams *spp = &ssd->sp;

    ftl_assert(ssd);

    ssd_init_params(spp, n);

    /* initialize ssd internal layout architecture */
    ssd->ch = g_malloc0(sizeof(struct ssd_channel) * spp->nchs);
    for (int i = 0; i < spp->nchs; i++) {
        ssd_init_ch(&ssd->ch[i], spp);
    } 

    /* initialize maptbl */
    ssd_init_maptbl(ssd);

    /* initialize rmap */
    ssd_init_rmap(ssd);

    /* initialize all the lines */
    ssd_init_lines(ssd);

	ssd_init_fdp_ru_mgmts(ssd); 					

	ssd_init_fdp_ruhtbl(n, ssd);				
    /* initialize write pointer, this is how we allocate new pages for writes */

    qemu_thread_create(&ssd->ftl_thread, "FEMU-FTL-Thread", ftl_thread, n,
                       QEMU_THREAD_JOINABLE);
}

static inline bool valid_ppa(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    int ch = ppa->g.ch;
    int lun = ppa->g.lun;
    int pl = ppa->g.pl;
    int blk = ppa->g.blk;
    int pg = ppa->g.pg;
    int sec = ppa->g.sec;

    if (ch >= 0 && ch < spp->nchs && lun >= 0 && lun < spp->luns_per_ch && pl >=
        0 && pl < spp->pls_per_lun && blk >= 0 && blk < spp->blks_per_pl && pg
        >= 0 && pg < spp->pgs_per_blk && sec >= 0 && sec < spp->secs_per_pg)
        return true;

    return false;
}

static inline bool valid_lpn(struct ssd *ssd, uint64_t lpn)
{
    return (lpn < ssd->sp.tt_pgs);
}

static inline bool mapped_ppa(struct ppa *ppa)
{
    return !(ppa->ppa == UNMAPPED_PPA);
}

static inline struct ssd_channel *get_ch(struct ssd *ssd, struct ppa *ppa)
{
    return &(ssd->ch[ppa->g.ch]);
}

static inline struct nand_lun *get_lun(struct ssd *ssd, struct ppa *ppa)
{
    struct ssd_channel *ch = get_ch(ssd, ppa);
    return &(ch->lun[ppa->g.lun]);
}

static inline struct nand_plane *get_pl(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_lun *lun = get_lun(ssd, ppa);
    return &(lun->pl[ppa->g.pl]);
}

static inline struct nand_block *get_blk(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_plane *pl = get_pl(ssd, ppa);
    return &(pl->blk[ppa->g.blk]);
}

static inline struct line *get_line(struct ssd *ssd, struct ppa *ppa)
{
    return &(ssd->lm.lines[ppa->g.blk]);
}

static inline struct ru *get_ru(struct ssd *ssd, struct ppa *ppa)
{
	struct ssdparams *spp = &ssd->sp;
	//uint16_t rgid = ppa->g.ch * (spp->luns_per_ch / RG_DEGREE) + (ppa->g.lun / RG_DEGREE);
	uint16_t rgid = (ppa->g.ch * spp->luns_per_ch + ppa->g.lun) / RG_DEGREE;
	struct ru_mgmt *rum = &ssd->rums[rgid];
	uint16_t ruid = ppa->g.blk;

    return &rum->rus[ruid];
}

static inline struct nand_page *get_pg(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = get_blk(ssd, ppa);
    return &(blk->pg[ppa->g.pg]);
}

static uint64_t ssd_advance_status(struct ssd *ssd, struct ppa *ppa, struct nand_cmd *ncmd)
{
    int c = ncmd->cmd;
    uint64_t cmd_stime = (ncmd->stime == 0) ? \
        qemu_clock_get_ns(QEMU_CLOCK_REALTIME) : ncmd->stime;
    uint64_t nand_stime;
    struct ssdparams *spp = &ssd->sp;
    struct nand_lun *lun = get_lun(ssd, ppa);
    uint64_t lat = 0;

    switch (c) {
    case NAND_READ:
        /* read: perform NAND cmd first */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->pg_rd_lat;
        lat = lun->next_lun_avail_time - cmd_stime;
#if 0
        lun->next_lun_avail_time = nand_stime + spp->pg_rd_lat;

        /* read: then data transfer through channel */
        chnl_stime = (ch->next_ch_avail_time < lun->next_lun_avail_time) ? \
            lun->next_lun_avail_time : ch->next_ch_avail_time;
        ch->next_ch_avail_time = chnl_stime + spp->ch_xfer_lat;

        lat = ch->next_ch_avail_time - cmd_stime;
#endif
        break;

    case NAND_WRITE:
        /* write: transfer data through channel first */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        if (ncmd->type == USER_IO) {
            lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;
        } else {
            lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;
        }
        lat = lun->next_lun_avail_time - cmd_stime;

#if 0
        chnl_stime = (ch->next_ch_avail_time < cmd_stime) ? cmd_stime : \
                     ch->next_ch_avail_time;
        ch->next_ch_avail_time = chnl_stime + spp->ch_xfer_lat;

        /* write: then do NAND program */
        nand_stime = (lun->next_lun_avail_time < ch->next_ch_avail_time) ? \
            ch->next_ch_avail_time : lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;

        lat = lun->next_lun_avail_time - cmd_stime;
#endif
        break;

    case NAND_ERASE:
        /* erase: only need to advance NAND status */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->blk_er_lat;

        lat = lun->next_lun_avail_time - cmd_stime;
        break;

    default:
        ftl_err("Unsupported NAND command: 0x%x\n", c);
    }

    return lat;
}

/* update SSD status about one page from PG_VALID -> PG_VALID */
static void mark_page_invalid(struct ssd *ssd, struct ppa *ppa, uint16_t rgid)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    bool was_full_ru = false;
	struct ru_mgmt *rum = &ssd->rums[rgid];
    struct ru *ru; 

	/* update corresponding page status */
	pg = get_pg(ssd, ppa);
	ftl_assert(pg->status == PG_VALID);
	pg->status = PG_INVALID;

	/* update corresponding block status */
	blk = get_blk(ssd, ppa);
	ftl_assert(blk->ipc >= 0 && blk->ipc < spp->pgs_per_blk);
	blk->ipc++;
	ftl_assert(blk->vpc > 0 && blk->vpc <= spp->pgs_per_blk);
	blk->vpc--;

	/* update corresponding ru status */
	ru = get_ru(ssd, ppa);
	ftl_assert(ru->ipc >= 0 && ru->ipc < spp->pgs_per_ru);
	if (ru->vpc == spp->pgs_per_ru) {
		ftl_assert(ru->ipc == 0);
		was_full_ru = true;
	}
	ru->ipc++;
	ftl_assert(ru->vpc > 0 && ru->vpc <= spp->pgs_per_ru);
	/* Adjust the position of the victime ru in the pq under over-writes */
	if (ru->pos) {
		/* Note that ru->vpc will be updated by this call */
		pqueue_change_priority(rum->victim_ru_pq, ru->vpc - 1, ru);
	} else {
		ru->vpc--;
	}

	if (was_full_ru) {
		/* move ru: "full" -> "victim" */
		QTAILQ_REMOVE(&rum->full_ru_list, ru, entry);
		rum->full_ru_cnt--;
		pqueue_insert(rum->victim_ru_pq, ru);
		rum->victim_ru_cnt++;
	}
}

static void mark_page_valid(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    struct ru *ru;

    /* update page status */
    pg = get_pg(ssd, ppa);
    ftl_assert(pg->status == PG_FREE);
    pg->status = PG_VALID;

    /* update corresponding block status */
    blk = get_blk(ssd, ppa);
    ftl_assert(blk->vpc >= 0 && blk->vpc < ssd->sp.pgs_per_blk);
    blk->vpc++;

	/* update corresponding ru status */
	ru = get_ru(ssd, ppa);
	ftl_assert(ru->vpc >= 0 && ru->vpc < ssd->sp.pgs_per_ru);
	ru->vpc++; 
} 

static void mark_block_free(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = get_blk(ssd, ppa);
    struct nand_page *pg = NULL;

    for (int i = 0; i < spp->pgs_per_blk; i++) {
        /* reset page status */
        pg = &blk->pg[i];
        ftl_assert(pg->nsecs == spp->secs_per_pg);
        pg->status = PG_FREE;
    }

    /* reset block status */
    ftl_assert(blk->npgs == spp->pgs_per_blk);
    blk->ipc = 0;
    blk->vpc = 0;
    blk->erase_cnt++;
}

static void gc_read_page(struct ssd *ssd, struct ppa *ppa)
{
    /* advance ssd status, we don't care about how long it takes */
    if (ssd->sp.enable_gc_delay) {
        struct nand_cmd gcr;
        gcr.type = GC_IO;
        gcr.cmd = NAND_READ;
        gcr.stime = 0;
        ssd_advance_status(ssd, ppa, &gcr);
    }
}

/* move valid page data (already in DRAM) from victim line to a new page */
static uint64_t fdp_gc_write_page(struct ssd *ssd, struct ppa *old_ppa, uint16_t rgid, uint16_t ruhid)
{
    struct ppa new_ppa;
    struct nand_lun *new_lun;
    uint64_t lpn = get_rmap_ent(ssd, old_ppa);

    ftl_assert(valid_lpn(ssd, lpn));

	new_ppa = get_new_page(ssd, rgid, ruhid, true);

    /* update maptbl */
    set_maptbl_ent(ssd, lpn, &new_ppa);

    /* update rmap */
    set_rmap_ent(ssd, lpn, &new_ppa);

	mark_page_valid(ssd, &new_ppa);

    /* need to advance the write pointer here */
	ssd_advance_ru_write_pointer(ssd, rgid, ruhid, true);

    if (ssd->sp.enable_gc_delay) {
        struct nand_cmd gcw;
        gcw.type = GC_IO;
        gcw.cmd = NAND_WRITE;
        gcw.stime = 0;
        ssd_advance_status(ssd, &new_ppa, &gcw);
    }

    new_lun = get_lun(ssd, &new_ppa);
    new_lun->gc_endtime = new_lun->next_lun_avail_time;

    return 0;
}

/* move valid page data (already in DRAM) from victim line to a new page */
static struct ru *select_victim_ru(struct ssd *ssd, bool force, int rgid)
{
    struct ru_mgmt *rum = &ssd->rums[rgid];
    struct ru *victim_ru = NULL;

    victim_ru = pqueue_peek(rum->victim_ru_pq);
    if (!victim_ru) {
        return NULL;
    } 

    if (!force && victim_ru->ipc < ssd->sp.pgs_per_ru / 8) {
        return NULL;
    }

    pqueue_pop(rum->victim_ru_pq);
    victim_ru->pos = 0;
    rum->victim_ru_cnt--;

    /* victim_ru is a danggling node now */
    return victim_ru;
}

/* here ppa identifies the block we want to clean */
static int clean_one_block(struct ssd *ssd, struct ppa *ppa, uint16_t rgid, uint16_t ruhid, uint64_t *moved_lpn_array,
                           int *moved_count)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_page *pg_iter = NULL;
    int cnt = 0;

    for (int pg = 0; pg < spp->pgs_per_blk; pg++) {
        ppa->g.pg = pg;
        pg_iter = get_pg(ssd, ppa);
        /* there shouldn't be any free page in victim blocks */
        ftl_assert(pg_iter->status != PG_FREE);
        if (pg_iter->status == PG_VALID) {
            uint64_t lpn = get_rmap_ent(ssd, ppa);
            gc_read_page(ssd, ppa);
            /* delay the maptbl update until "write" happens */
            fdp_gc_write_page(ssd, ppa, rgid, ruhid);
            cnt++;
            moved_lpn_array[*moved_count] = lpn;
            (*moved_count)++;
        }
    }

    ftl_assert(get_blk(ssd, ppa)->vpc == cnt);
    return cnt;
}

static int do_gc(struct ssd *ssd, uint16_t rgid, bool force, NvmeRequest *req)
{
	struct ru *victim_ru = NULL;
	struct ssdparams *spp = &ssd->sp;
	struct nand_lun *lunp; 
	struct ppa ppa;
	struct ru_mgmt *rum = &ssd->rums[rgid];
	NvmeRuHandle *ruh;
	NvmeNamespace *ns = req->ns;
	int start_lunidx = rgid * RG_DEGREE;
	uint16_t ruhid;

    // int startLba = req->slba; // FDP LOG 

	victim_ru = select_victim_ru(ssd, force, rgid);
	if (!victim_ru) {
		return -1;
	}

    ppa.g.blk = victim_ru->id;
	ruhid = victim_ru->ruhid; 
	ruh = &ns->endgrp->fdp.ruhs[ruhid];	

    ftl_debug("GC-ing line:%d,ipc=%d,victim=%d,full=%d,free=%d\n", ppa.g.blk,
              victim_line->ipc, ssd->lm.victim_line_cnt, ssd->lm.full_line_cnt,
              ssd->lm.free_line_cnt);

    // FDP LOG
    int max_entries = RG_DEGREE * spp->pgs_per_blk;
    uint64_t *moved_lpn_array = calloc(max_entries, sizeof(uint64_t));
    int moved_count = 0;

    for (int lunidx = start_lunidx; lunidx < start_lunidx + RG_DEGREE; lunidx++) {
		ppa.g.ch = lunidx / spp->luns_per_ch;
		ppa.g.lun = lunidx % spp->luns_per_ch;
		ppa.g.pl = 0;
		lunp = get_lun(ssd, &ppa);
        int movedPages = clean_one_block(ssd, &ppa, rgid, ruhid, moved_lpn_array, &moved_count); // FDP LOG
        uint64_t gc_bytes = ssd->sp.secs_per_pg * ssd->sp.secsz;  // size of one page
        ns->endgrp->fdp.mbmw += gc_bytes * movedPages;

        mark_block_free(ssd, &ppa);

		if (spp->enable_gc_delay) {
			struct nand_cmd gce;
			gce.type = GC_IO;
			gce.cmd = NAND_ERASE;
			gce.stime = 0;
			ssd_advance_status(ssd, &ppa, &gce);
		} 

		lunp->gc_endtime = lunp->next_lun_avail_time;
	} 

	if (ruh->ruht == NVME_RUHT_INITIALLY_ISOLATED && log_event(ruh, FDP_EVT_MEDIA_REALLOC)) {
		/* 4. FDP Event logging */
		// /*****************
		NvmeFdpEvent *e = nvme_fdp_alloc_event(req->ns->ctrl, &ns->endgrp->fdp.ctrl_events);
        uint16_t largest_contiguous_lba_start;
        uint64_t nlbam;
        if (e)
        {
            // Set event fields
            e->type = FDP_EVT_MEDIA_REALLOC;

            // Set PIV, NSIDV, LV
            e->flags = FDPEF_PIV | FDPEF_NSIDV | FDPEF_LV;

            

            // largest_contiguous_lba_start and nlbam
            if (moved_count > 0) {
                int max_run = 1;
                int current_run = 1;
                uint64_t max_start_lpn = moved_lpn_array[0];
                for (int i = 1; i < moved_count; i++)
                {
                    if (moved_lpn_array[i] == moved_lpn_array[i - 1] + 1)
                    {
                        current_run++;
                    }
                    else
                    {
                        if (current_run > max_run)
                        {
                            max_run = current_run;
                            max_start_lpn = moved_lpn_array[i - current_run];
                        }
                        current_run = 1;
                    }
                }

                if (current_run > max_run)
                {
                    max_run = current_run;
                    max_start_lpn = moved_lpn_array[moved_count - current_run];
                }

                largest_contiguous_lba_start = max_start_lpn * spp->secs_per_pg;
                nlbam = (uint64_t)max_run * spp->secs_per_pg;
            }
            
            e->pid = largest_contiguous_lba_start;
            e->timestamp = nlbam;

            e->nsid = ns->id;
            e->rgid = rgid;
            e->ruhid = ruhid;
        }
        // *****************/
	}

	/* reset wp of victim ru */
	victim_ru->wp.ch = start_lunidx / spp->luns_per_ch;
	victim_ru->wp.lun = start_lunidx % spp->luns_per_ch;
	victim_ru->wp.pl = 0;
	victim_ru->wp.blk = victim_ru->id;
	victim_ru->wp.pg = 0;

    /* update ru status */
	victim_ru->ipc = 0;
	victim_ru->vpc = 0;
	QTAILQ_INSERT_TAIL(&rum->free_ru_list, victim_ru, entry);
	rum->free_ru_cnt++;

	return 0;
}

static uint64_t ssd_read(struct ssd *ssd, NvmeRequest *req)
{
    struct ssdparams *spp = &ssd->sp;
    uint64_t lba = req->slba;
    int nsecs = req->nlb;
    struct ppa ppa;
    uint64_t start_lpn = lba / spp->secs_per_pg;
    uint64_t end_lpn = (lba + nsecs - 1) / spp->secs_per_pg;
    uint64_t lpn;
    uint64_t sublat, maxlat = 0;

    if (end_lpn >= spp->tt_pgs) {
        ftl_err("start_lpn=%"PRIu64",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
    }

    /* normal IO read path */
    for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
        ppa = get_maptbl_ent(ssd, lpn);
        if (!mapped_ppa(&ppa) || !valid_ppa(ssd, &ppa)) {
            continue;
        }

        struct nand_cmd srd;
        srd.type = USER_IO;
        srd.cmd = NAND_READ;
        srd.stime = req->stime;
        sublat = ssd_advance_status(ssd, &ppa, &srd);
        maxlat = (sublat > maxlat) ? sublat : maxlat;
    }

    return maxlat; 
}

static uint64_t ssd_write(struct ssd *ssd, NvmeRequest *req)
{
	uint64_t lba = req->slba;
	struct ssdparams *spp = &ssd->sp;
    int len = req->nlb;
    uint64_t start_lpn = lba / spp->secs_per_pg;
    uint64_t end_lpn = (lba + len - 1) / spp->secs_per_pg;
    struct ppa ppa;
    uint64_t lpn;
    uint64_t curlat = 0, maxlat = 0;
    int r = 0;
	uint16_t ruhid;										

	NvmeNamespace *ns = req->ns;
	NvmeEnduranceGroup *endgrp = ns->endgrp;
	NvmeRwCmd *rw = (NvmeRwCmd*)&req->cmd;				

	/* 1. DTYPE & PID parsing */
	// /******************************
    uint8_t dtype = 0x02;
	uint16_t pid = rw->dspec;                   // Placement ID -> specifies a RG and placement handle referencing a unique RU
	uint16_t rgif = endgrp->fdp.rgif;           // RG id format
    uint16_t ph_bits = 16 - rgif;
    uint16_t rgid = pid >> ph_bits;      // RG id
    uint16_t ph = pid & ((1 << ph_bits) - 1);   // Placement handler
    // *******************************/

    if (dtype != NVME_DIRECTIVE_DATA_PLACEMENT) {
		ph = 0;
		rgid = 0;
	}

	ruhid = ns->fdp.phs[ph];						

    if (end_lpn >= spp->tt_pgs) {
		ftl_err("start_lpn=%"PRIu64",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
	} 

	/* perform GC here until !should_gc(ssd, rgid) */
	while (should_gc_high(ssd, rgid)) {
		r = do_gc(ssd, rgid, true, req);
		ftl_assert(spp->tt_valid_pgs >= 0);
		if (r == -1)
			break;
	}

    // FDP LOG
    uint64_t bytes_written = (uint64_t)len * ssd->sp.secsz;
    ns->endgrp->fdp.hbmw += bytes_written;
    ns->endgrp->fdp.mbmw += bytes_written;

    for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
        ppa = get_maptbl_ent(ssd, lpn);
        if (mapped_ppa(&ppa)) {
            /* update old page information first */
			uint16_t old_rgid = (ppa.g.ch * spp->luns_per_ch + ppa.g.lun) / RG_DEGREE;
			mark_page_invalid(ssd, &ppa, old_rgid); 
            set_rmap_ent(ssd, INVALID_LPN, &ppa);
        }

        /* new write */
		ppa = get_new_page(ssd, rgid, ruhid, false);

        /* update maptbl */
        set_maptbl_ent(ssd, lpn, &ppa);
        /* update rmap */
        set_rmap_ent(ssd, lpn, &ppa);

        mark_page_valid(ssd, &ppa);

        /* need to advance the write pointer here */
		ssd_advance_ru_write_pointer(ssd, rgid, ruhid, false);

        struct nand_cmd swr;
        swr.type = USER_IO;
        swr.cmd = NAND_WRITE;
        swr.stime = req->stime;
        /* get latency statistics */
        curlat = ssd_advance_status(ssd, &ppa, &swr);
        maxlat = (curlat > maxlat) ? curlat : maxlat;
    }

    return maxlat;
}

static void *ftl_thread(void *arg)
{
    FemuCtrl *n = (FemuCtrl *)arg;
    struct ssd *ssd = n->ssd;
    NvmeRequest *req = NULL;
    uint64_t lat = 0;
    int rc;
    int i;

    while (!*(ssd->dataplane_started_ptr)) {
        usleep(100000);
    }

    /* FIXME: not safe, to handle ->to_ftl and ->to_poller gracefully */
    ssd->to_ftl = n->to_ftl;
    ssd->to_poller = n->to_poller;

    while (1) {
        for (i = 1; i <= n->nr_pollers; i++) {
            if (!ssd->to_ftl[i] || !femu_ring_count(ssd->to_ftl[i]))
                continue;

            rc = femu_ring_dequeue(ssd->to_ftl[i], (void *)&req, 1);
            if (rc != 1) {
                printf("FEMU: FTL to_ftl dequeue failed\n");
			}

			ftl_assert(req);
			switch (req->cmd.opcode) {
			case NVME_CMD_WRITE:
                lat = ssd_write(ssd, req);
                break;
            case NVME_CMD_READ:
                lat = ssd_read(ssd, req);
                break;
            case NVME_CMD_DSM:
                lat = 0;
                break;
            default:
                ftl_err("FTL received unkown request type (opcode: %d), ERROR\n", req->cmd.opcode);
            }

            req->reqlat = lat;
            req->expire_time += lat;

            rc = femu_ring_enqueue(ssd->to_poller[i], (void *)&req, 1);
            if (rc != 1) {
                ftl_err("FTL to_poller enqueue failed\n");
            }
        }
    }

    return NULL;
}
