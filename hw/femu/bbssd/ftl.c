#include "ftl.h"

#define FEMU_DEBUG_FTL

static void *ftl_thread(void *arg);

static uint64_t ssd_advance_status(struct ssd *ssd, struct ppa *ppa, struct nand_cmd *ncmd);

static struct ppa get_new_page(struct ssd *ssd);
static void ssd_advance_write_pointer(struct ssd *ssd);

/* Garbage Collection Functions */
static inline bool should_gc(struct ssd *ssd);
static inline bool should_gc_high(struct ssd *ssd);
static bool should_gc_translation(struct ssd *ssd);
static int translation_gc(struct ssd *ssd);

/* Hash Functions */
static inline int cmt_hash_func(uint64_t dlpn);
static inline int ctp_hash_func(uint64_t dlpn);

/* CMT (Cached Mapping Table) Functions */
static struct cmt_entry *find_cmt_entry(struct cmt *cmt_struct, uint64_t dlpn);
static void move_cmt_entry_to_tail(struct cmt *cmt_struct, struct cmt_entry *entry);
static void evict_cmt_entry(struct ssd *ssd);
static void insert_cmt_entry(struct ssd *ssd, uint64_t dlpn, struct ppa dppn, bool dirty);
static void remove_cmt_entry(struct ssd *ssd, struct cmt_entry *entry);

/* CTP (Cached Translation Page) Functions */
static void evict_ctp_entry(struct ctp *ctp_struct, struct ssd *ssd);
static void insert_ctp_entry(struct ctp *ctp_struct, struct ctp_entry *entry, struct ssd *ssd);
static struct ctp_entry *find_ctp_entry(struct ctp *ctp_struct, uint64_t tvpn);
static void move_ctp_entry_to_tail(struct ctp *ctp_struct, struct ctp_entry *entry);

/* Translation Page Read/Write Functions */
static void write_translation_page(struct ssd *ssd, struct ppa *tppa, struct map_page *mp);
static struct map_page *read_translation_page(struct ssd *ssd, struct ppa *tppa);

static inline bool should_gc(struct ssd *ssd)
{
    return (ssd->lm.free_line_cnt <= ssd->sp.gc_thres_lines);
}

static inline bool should_gc_high(struct ssd *ssd)
{
    return (ssd->lm.free_line_cnt <= ssd->sp.gc_thres_lines_high);
}

static bool should_gc_translation(struct ssd *ssd)
{
    struct write_pointer *twp = &ssd->trans_wp;
    // Translation block이 거의 다 찼을 때 GC 시작
    return (twp->pg >= ssd->sp.pgs_per_blk - 1);
}
static void translation_gc(struct ssd *ssd)
{
    // Select victim block (e.g., the block with the least valid pages)
    int victim_blk_idx = -1;
    int min_valid_pages = 257; // More than the max valid pages

    for (int i = 0; i < 16; i++)
    {
        struct translation_block *blk = &ssd->translation_blocks[i];
        if (blk->valid_pages > 0 && blk->valid_pages < min_valid_pages)
        {
            victim_blk_idx = i;
            min_valid_pages = blk->valid_pages;
        }
    }

    if (victim_blk_idx == -1)
    {
        fprintf(stderr, "No victim block found for translation GC.\n");
        return;
    }

    struct translation_block *victim_blk = &ssd->translation_blocks[victim_blk_idx];

    // Find a free block to copy valid pages into
    int free_blk_idx = -1;
    for (int i = 0; i < 16; i++)
    {
        struct translation_block *blk = &ssd->translation_blocks[i];
        if (!blk->is_full && i != victim_blk_idx)
        {
            free_blk_idx = i;
            break;
        }
    }

    if (free_blk_idx == -1)
    {
        fprintf(stderr, "No free translation blocks available for GC.\n");
        return;
    }

    struct translation_block *free_blk = &ssd->translation_blocks[free_blk_idx];

    // Copy valid pages
    for (int page_idx = 0; page_idx < 256; page_idx++)
    {
        struct translation_page *victim_page = &victim_blk->pages[page_idx];
        if (victim_page->mp != NULL && victim_page->mp->dppn != NULL)
        {
            // Find a free page in free_blk
            int free_page_idx = -1;
            for (int i = 0; i < 256; i++)
            {
                if (free_blk->pages[i].mp == NULL)
                {
                    free_page_idx = i;
                    break;
                }
            }
            if (free_page_idx == -1)
            {
                fprintf(stderr, "No free pages in free translation block.\n");
                break;
            }

            struct translation_page *free_page = &free_blk->pages[free_page_idx];

            // Copy the map_page
            free_page->mp = malloc(sizeof(struct map_page));
            if (!free_page->mp)
            {
                fprintf(stderr, "Failed to allocate memory for map_page during GC.\n");
                exit(EXIT_FAILURE);
            }

            free_page->mp->dppn = malloc(sizeof(struct ppa) * 512);
            if (!free_page->mp->dppn)
            {
                fprintf(stderr, "Failed to allocate memory for dppn array during GC.\n");
                exit(EXIT_FAILURE);
            }

            memcpy(free_page->mp->dppn, victim_page->mp->dppn, sizeof(struct ppa) * 512);

            // Update tppn
            free_page->tppn.ppa = free_blk_idx * 256 + free_page_idx;
            free_page->tvpn = victim_page->tvpn;

            // Update GTD
            uint64_t tvpn = victim_page->tvpn;
            ssd->gtd[tvpn].tppn = free_page->tppn;

            // Invalidate the victim page
            free(victim_page->mp->dppn);
            free(victim_page->mp);
            victim_page->mp = NULL;
            victim_page->tppn.ppa = UNMAPPED_PPA;
            victim_page->tvpn = INVALID_TVPN;

            // Update valid_pages counts
            victim_blk->valid_pages--;
            free_blk->valid_pages++;

            if (free_blk->valid_pages == 256)
            {
                free_blk->is_full = true;
                ssd->free_translation_blocks--;
            }
        }
    }

    // Erase the victim block
    victim_blk->valid_pages = 0;
    victim_blk->is_full = false;
    ssd->free_translation_blocks++;

    // Free any residual pages
    for (int page_idx = 0; page_idx < 256; page_idx++)
    {
        struct translation_page *page = &victim_blk->pages[page_idx];
        if (page->mp != NULL)
        {
            if (page->mp->dppn != NULL)
            {
                free(page->mp->dppn);
            }
            free(page->mp);
            page->mp = NULL;
        }
        page->tppn.ppa = UNMAPPED_PPA;
        page->tvpn = INVALID_TVPN;
    }
}
/* Calculate hash bucket */
static inline int cmt_hash_func(uint64_t dlpn)
{
    return (int)(dlpn % 10);
}

static inline int ctp_hash_func(uint64_t dlpn)
{
    return (int)(dlpn % 32);
}

/* Find cmt entry in cmt_hash_table */
static struct cmt_entry *find_cmt_entry(struct cmt *cmt_struct, uint64_t dlpn)
{
    int index = cmt_hash_func(dlpn);
    struct cmt_entry *entry = cmt_struct->hash_table[index].cmt_entries;

    while (entry)
    {
        if (entry->data.dlpn == dlpn)
        {
            return entry;
        }
        entry = entry->next;
    }
    return NULL;
}

/* Node is accessed -> move to tail  */
static void move_cmt_entry_to_tail(struct cmt *cmt_struct, struct cmt_entry *entry)
{
    // Already in tail
    if (!entry || entry == cmt_struct->lru_tail)
    {
        return;
    }

    // prev is old, next is new

    // Remove the entry from its current position in LRU list
    if (entry->lru_prev)
    {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    else
    {
        cmt_struct->lru_head = entry->lru_next;
    }
    if (entry->lru_next)
    {
        entry->lru_next->lru_prev = entry->lru_prev;
    }
    else
    {
        cmt_struct->lru_tail = entry->lru_prev;
    }

    // Place it at the tail
    entry->lru_prev = cmt_struct->lru_tail;
    entry->lru_next = NULL;
    if (cmt_struct->lru_tail)
    {
        cmt_struct->lru_tail->lru_next = entry;
    }
    else
    {
        cmt_struct->lru_head = entry;
    }
    cmt_struct->lru_tail = entry;
}

static void evict_cmt_entry(struct ssd *ssd)
{
    struct cmt *cmt_struct = ssd->cmt;
    struct cmt_entry *victim = cmt_struct->lru_head;
    if (!victim)
    {
        return;
    }

    // Remove from the LRU list
    cmt_struct->lru_head = victim->lru_next;
    if (cmt_struct->lru_head)
    {
        cmt_struct->lru_head->lru_prev = NULL;
    }
    else
    {
        cmt_struct->lru_tail = NULL;
    }

    // Remove from the hash table
    int index = cmt_hash_func(victim->data.dlpn);
    struct cmt_entry **bucket_entry = &cmt_struct->hash_table[index].cmt_entries;
    while (*bucket_entry && (*bucket_entry)->data.dlpn != victim->data.dlpn)
    {
        bucket_entry = &(*bucket_entry)->next;
    }
    if (*bucket_entry)
    {
        *bucket_entry = (*bucket_entry)->next;
    }

    // If victim is dirty, flush the mapping
    if (victim->data.dirty)
    {
        // Flush the translation mapping table
        ssd->trans_maptbl[victim->data.dlpn] = victim->data.dppn;
        victim->data.dirty = false;
    }

    g_free(victim);
    cmt_struct->current_size--;
}

static void insert_cmt_entry(struct ssd *ssd, uint64_t dlpn, struct ppa dppn, bool dirty)
{
    struct cmt *cmt_struct = ssd->cmt;
    struct cmt_entry *entry = find_cmt_entry(cmt_struct, dlpn);
    if (entry)
    {
        // Update existing entry
        entry->data.dppn = dppn;
        entry->data.dirty = dirty;
        move_cmt_entry_to_tail(cmt_struct, entry);
        return;
    }

    // If capacity is exceeded, evict the least recently used item
    if (cmt_struct->current_size >= cmt_struct->max_entries)
    {
        evict_cmt_entry(ssd);
    }

    // Create a new entry
    entry = g_malloc0(sizeof(struct cmt_entry));
    entry->data.dlpn = dlpn;
    entry->data.dppn = dppn;
    entry->data.dirty = dirty;

    // Insert into the hash table
    int index = cmt_hash_func(dlpn);
    entry->next = cmt_struct->hash_table[index].cmt_entries;
    if (entry->next)
    {
        entry->next->prev = entry;
    }
    cmt_struct->hash_table[index].cmt_entries = entry;

    // Insert into LRU list at the tail
    entry->lru_prev = cmt_struct->lru_tail;
    entry->lru_next = NULL;
    if (cmt_struct->lru_tail)
    {
        cmt_struct->lru_tail->lru_next = entry;
    }
    else
    {
        cmt_struct->lru_head = entry;
    }
    cmt_struct->lru_tail = entry;

    cmt_struct->current_size++;
}
/* Remove an entry from CMT */
static void remove_cmt_entry(struct ssd *ssd, struct cmt_entry *entry)
{
    if (!entry)
        return;

    // Update the LRU list
    if (entry->lru_prev)
    {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    else
    {
        ssd->cmt->lru_head = entry->lru_next;
    }
    if (entry->lru_next)
    {
        entry->lru_next->lru_prev = entry->lru_prev;
    }
    else
    {
        ssd->cmt->lru_tail = entry->lru_prev;
    }

    // Remove from hash table
    uint64_t index = cmt_hash_func(entry->data.dlpn);
    struct cmt_entry **bucket_entry = &ssd->cmt->hash_table[index].cmt_entries;
    while (*bucket_entry && (*bucket_entry)->data.dlpn != entry->data.dlpn)
    {
        bucket_entry = (struct cmt_entry **)&(*bucket_entry)->next;
    }
    if (*bucket_entry)
    {
        *bucket_entry = (struct cmt_entry *)(*bucket_entry)->next;
    }

    g_free(entry);
    ssd->cmt->current_size--;
}

static void evict_ctp_entry(struct ctp *ctp_struct, struct ssd *ssd)
{
    struct ctp_entry *victim = ctp_struct->lru_head;
    if (!victim)
        return; // Nothing to evict

    // Update the LRU list
    ctp_struct->lru_head = victim->lru_next;
    if (ctp_struct->lru_head)
    {
        ctp_struct->lru_head->lru_prev = NULL;
    }
    else
    {
        ctp_struct->lru_tail = NULL;
    }

    // Remove from hash table
    int index = ctp_hash_func(victim->tvpn);
    struct ctp_entry *entry = ctp_struct->hash_table[index].ctp_entries;
    struct ctp_entry *prev_entry = NULL;
    while (entry && entry->tvpn != victim->tvpn)
    {
        prev_entry = entry;
        entry = entry->next;
    }
    if (entry)
    {
        if (prev_entry)
        {
            prev_entry->next = entry->next;
        }
        else
        {
            ctp_struct->hash_table[index].ctp_entries = entry->next;
        }
        if (entry->next)
        {
            entry->next->prev = prev_entry;
        }
    }

    // Flush to translation block if dirty
    if (victim->dirty)
    {
        // Write the translation page to flash
        write_translation_page(ssd, &victim->tppn, victim->mp);

        // Update translation mapping table
        ssd->trans_maptbl[victim->tvpn] = victim->tppn;

        // Update GTD
        ssd->gtd[victim->tvpn].tppn = victim->tppn;
        ssd->gtd[victim->tvpn].location = 1;  // Now on flash
        ssd->gtd[victim->tvpn].dirty = false; // Clean after flush
    }
    else
    {
        // No need to flush; update GTD
        ssd->gtd[victim->tvpn].location = 1; // On flash
    }

    g_free(victim->mp->dppn);
    g_free(victim->mp);
    g_free(victim);
    ctp_struct->current_size--;
}

static void insert_ctp_entry(struct ctp *ctp_struct, struct ctp_entry *entry, struct ssd *ssd)
{
    if (ctp_struct->current_size >= ctp_struct->max_entries)
    {
        evict_ctp_entry(ctp_struct, ssd);
    }

    int index = ctp_hash_func(entry->tvpn);
    entry->next = ctp_struct->hash_table[index].ctp_entries;
    if (entry->next)
    {
        entry->next->prev = entry;
    }
    ctp_struct->hash_table[index].ctp_entries = entry;

    entry->lru_prev = ctp_struct->lru_tail;
    entry->lru_next = NULL;
    if (ctp_struct->lru_tail)
    {
        ctp_struct->lru_tail->lru_next = entry;
    }
    else
    {
        ctp_struct->lru_head = entry;
    }
    ctp_struct->lru_tail = entry;

    ctp_struct->current_size++;
}

static struct ctp_entry *find_ctp_entry(struct ctp *ctp_struct, uint64_t tvpn)
{
    int index = ctp_hash_func(tvpn);
    struct ctp_entry *entry = ctp_struct->hash_table[index].ctp_entries;

    while (entry)
    {
        if (entry->tvpn == tvpn)
        {
            return entry;
        }
        entry = entry->next;
    }
    return NULL;
}

// Translation page를 flash에 쓰기
static void write_translation_page(struct ssd *ssd, struct ppa *tppa, struct map_page *mp, uint64_t tvpn)
{
    // Check if current translation block is full
    while (ssd->translation_blocks[ssd->current_translation_block].is_full)
    {
        // Advance to the next block
        ssd->current_translation_block = (ssd->current_translation_block + 1) % 16;

        // If all blocks are full, perform garbage collection
        if (ssd->free_translation_blocks == 0)
        {
            translation_gc(ssd);
        }
    }

    struct translation_block *curr_blk = &ssd->translation_blocks[ssd->current_translation_block];

    // Find the next free page in the current block
    int page_idx = -1;
    for (int i = 0; i < 256; i++)
    {
        if (curr_blk->pages[i].mp == NULL || curr_blk->pages[i].mp->dppn == NULL)
        {
            page_idx = i;
            break;
        }
    }

    if (page_idx == -1)
    {
        // Current block is full, mark it and retry
        curr_blk->is_full = true;
        ssd->free_translation_blocks--;
        write_translation_page(ssd, tppa, mp, tvpn);
        return;
    }

    struct translation_page *page = &curr_blk->pages[page_idx];

    // Free existing mp if any
    if (page->mp != NULL)
    {
        if (page->mp->dppn != NULL)
        {
            free(page->mp->dppn);
        }
        free(page->mp);
    }

    // Assign the new map_page
    page->mp = malloc(sizeof(struct map_page));
    if (!page->mp)
    {
        fprintf(stderr, "Failed to allocate memory for map_page.\n");
        exit(EXIT_FAILURE);
    }

    page->mp->dppn = malloc(sizeof(struct ppa) * 512);
    if (!page->mp->dppn)
    {
        fprintf(stderr, "Failed to allocate memory for dppn array.\n");
        exit(EXIT_FAILURE);
    }

    // Copy the mappings
    memcpy(page->mp->dppn, mp->dppn, sizeof(struct ppa) * 512);

    // Assign tppn
    page->tppn.ppa = ssd->current_translation_block * 256 + page_idx;

    // Assign tvpn
    page->tvpn = tvpn;

    // Update tppa (output parameter)
    tppa->ppa = page->tppn.ppa;

    // Update GTD
    ssd->gtd[tvpn].tppn = page->tppn;
    ssd->gtd[tvpn].dirty = false;

    // Update block metadata
    curr_blk->valid_pages++;
    if (curr_blk->valid_pages == 256)
    {
        curr_blk->is_full = true;
        ssd->free_translation_blocks--;
    }

    // Mark the page as valid
    page->dirty = false;
}

// Translation page를 flash에서 읽기
static struct map_page *read_translation_page(struct ssd *ssd, struct ppa *tppa)
{
    uint64_t tppn = tppa->ppa;
    int blk_idx = tppn / 256;
    int page_idx = tppn % 256;

    if (blk_idx < 0 || blk_idx >= 16 || page_idx < 0 || page_idx >= 256)
    {
        fprintf(stderr, "Invalid tppn: blk_idx=%d, page_idx=%d\n", blk_idx, page_idx);
        return NULL;
    }

    struct translation_block *blk = &ssd->translation_blocks[blk_idx];
    struct translation_page *page = &blk->pages[page_idx];

    if (page->mp == NULL || page->mp->dppn == NULL)
    {
        fprintf(stderr, "Translation page not found at tppn=%lu\n", tppn);
        return NULL;
    }

    return page->mp;
}

static void move_ctp_entry_to_tail(struct ctp *ctp_struct, struct ctp_entry *entry)
{
    if (!entry || entry == ctp_struct->lru_tail)
    {
        return;
    }

    if (entry->lru_prev)
    {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    else
    {
        ctp_struct->lru_head = entry->lru_next;
    }
    if (entry->lru_next)
    {
        entry->lru_next->lru_prev = entry->lru_prev;
    }
    else
    {
        ctp_struct->lru_tail = entry->lru_prev;
    }

    entry->lru_prev = ctp_struct->lru_tail;
    entry->lru_next = NULL;
    if (ctp_struct->lru_tail)
    {
        ctp_struct->lru_tail->lru_next = entry;
    }
    else
    {
        ctp_struct->lru_head = entry;
    }
    ctp_struct->lru_tail = entry;
}

static inline struct ppa get_maptbl_ent(struct ssd *ssd, uint64_t lpn)
{
    // return ssd->maptbl[lpn];

    struct ppa ppa;

    // Look in CMT
    struct cmt_entry *entry = find_cmt_entry(ssd->cmt, lpn);
    if (entry)
    {
        move_cmt_entry_to_tail(ssd->cmt, entry);
        if (entry->data.dppn.ppa != ssd->maptbl[lpn].ppa)
        {
            fprintf(stderr, "Error: CMT mismatch! entry->data.dppn.ppa = %lu, ssd->maptbl[lpn].ppa = %lu\n",
                    entry->data.dppn.ppa, ssd->maptbl[lpn].ppa);
        }
        // return entry->data.dppn;
        return ssd->maptbl[lpn];
    }

    uint64_t tvpn = lpn / 512;

    struct gtd_entry *gtd_entry = &ssd->gtd[tvpn];
    // unmapped ppn
    if (gtd_entry->tppn.ppa == UNMAPPED_PPA)
    {
        // not found anywhere
        ppa.ppa = UNMAPPED_PPA;
        // return ppa;
        return ssd->maptbl[lpn];
    }

    // Look in CTP
    if (gtd_entry->location == 0)
    {
        struct ctp_entry *ctp_entry = find_ctp_entry(ssd->ctp, tvpn);
        if (ctp_entry)
        {
            move_ctp_entry_to_tail(ssd->ctp, ctp_entry);
            uint64_t offset = lpn % 512;
            ppa = ctp_entry->mp->dppn[offset];

            if (ppa.ppa != ssd->maptbl[lpn].ppa)
            {
                fprintf(stderr, "Error: CTP mismatch! ppa = %lu, ssd->maptbl[lpn].ppa = %lu\n", ppa.ppa,
                        ssd->maptbl[lpn].ppa);
            }

            insert_cmt_entry(ssd, lpn, ppa, false);
            // return ppa;
            return ssd->maptbl[lpn];
        }
    }
    else
    {
        // Load translation page from flash
        struct ctp_entry *ctp_ent = g_malloc0(sizeof(struct ctp_entry));
        ctp_ent->tvpn = tvpn;
        ctp_ent->tppn = gtd_entry->tppn;
        ctp_ent->mp = read_translation_page(ssd, &gtd_entry->tppn);
        ctp_ent->dirty = false;
        insert_ctp_entry(ssd->ctp, ctp_ent, ssd);

        ssd->gtd[tvpn].location = 0;

        ppa = ctp_ent->mp->dppn[lpn % 512];

        if (ppa.ppa != ssd->maptbl[lpn].ppa)
        {
            fprintf(stderr, "Error: FLASH mismatch! ppa = %lu, ssd->maptbl[lpn].ppa = %lu\n", ppa.ppa,
                    ssd->maptbl[lpn].ppa);
        }

        insert_cmt_entry(ssd, lpn, ppa, false);

        // return ppa;
        return ssd->maptbl[lpn];
    }

    // not found anywhere
    ppa.ppa = UNMAPPED_PPA;
    // return ppa;
    return ssd->maptbl[lpn];
}

static inline void set_maptbl_ent(struct ssd *ssd, uint64_t lpn, struct ppa *new_ppa)
{
    ftl_assert(lpn < ssd->sp.tt_pgs);
    ssd->maptbl[lpn] = *new_ppa;

    uint64_t tvpn = lpn / 512;

    struct ctp_entry *ctp_ent = find_ctp_entry(ssd->ctp, tvpn);
    if (ctp_ent)
    {
        // Tdemand is in CTP
        // Replace RDppn with RD'_ppn in CTP
        ctp_ent->mp->dppn[lpn % 512] = *new_ppa;
        ctp_ent->dirty = true; // Mark the translation page as dirty
        move_ctp_entry_to_tail(ssd->ctp, ctp_ent);

        // Check if (RDlpn, RDppn) is in CMT
        struct cmt_entry *cmt_ent = find_cmt_entry(ssd->cmt, lpn);
        if (cmt_ent)
        {
            // Erase (RDlpn, RDppn) from CMT
            remove_cmt_entry(ssd, cmt_ent);

            // CTP hit and CMT hit
        }
    }
    else
    {
        // Tdemand is not in CTP
        // CTP miss
        // Check if (RDlpn, RDppn) is in CMT
        struct cmt_entry *cmt_ent = find_cmt_entry(ssd->cmt, lpn);
        struct gtd_entry *gtd_ent = &ssd->gtd[tvpn];
        if (cmt_ent)
        {
            // Replace ppn in CMT
            cmt_ent->data.dppn = *new_ppa;
            cmt_ent->data.dirty = true;
            move_cmt_entry_to_tail(ssd->cmt, cmt_ent);

            // CTP miss and CMT hit
        }
        else
        {
            // Fetch Tdemand into CTP
            if (gtd_ent->tppn.ppa != UNMAPPED_PPA)
            {
                // Load translation page from flash
                struct ppa tppn = ssd->trans_maptbl[tvpn];
                if (tppn.ppa == UNMAPPED_PPA)
                {
                    // Translation page does not exist
                    return;
                }

                ctp_ent = g_malloc0(sizeof(struct ctp_entry));
                ctp_ent->tvpn = tvpn;
                ctp_ent->tppn = tppn;
                ctp_ent->dirty = false;
                ctp_ent->mp = read_translation_page(ssd, &tppn);
            }
            else
            {
                // Translation page does not exist; create a new one
                ctp_ent = g_malloc0(sizeof(struct ctp_entry));
                ctp_ent->tvpn = tvpn;
                ctp_ent->mp = g_malloc0(sizeof(struct map_page));
                ctp_ent->mp->dppn = g_malloc0(sizeof(struct ppa) * 512);
                for (int i = 0; i < 512; i++)
                {
                    ctp_ent->mp->dppn[i].ppa = UNMAPPED_PPA;
                }
            }

            ctp_ent->tppn = gtd_ent->tppn;
            ctp_ent->dirty = true;
            insert_ctp_entry(ssd->ctp, ctp_ent, ssd);

            // Replace ppn in CTP
            ctp_ent->mp->dppn = new_ppa;
            move_ctp_entry_to_tail(ssd->ctp, ctp_ent);
        }
    }

    // Update GTD
    struct gtd_entry *gtd_ent = &ssd->gtd[tvpn];
    gtd_ent->dirty = true;
}

static uint64_t ppa2pgidx(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    uint64_t pgidx;

    pgidx = ppa->g.ch * spp->pgs_per_ch + ppa->g.lun * spp->pgs_per_lun + ppa->g.pl * spp->pgs_per_pl +
            ppa->g.blk * spp->pgs_per_blk + ppa->g.pg;

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
    lm->victim_line_pq = pqueue_init(spp->tt_lines, victim_line_cmp_pri, victim_line_get_pri, victim_line_set_pri,
                                     victim_line_get_pos, victim_line_set_pos);
    QTAILQ_INIT(&lm->full_line_list);

    lm->free_line_cnt = 0;
    for (int i = 0; i < lm->tt_lines; i++)
    {
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

static void ssd_init_write_pointer(struct ssd *ssd)
{
    struct write_pointer *wpp = &ssd->wp;
    struct line_mgmt *lm = &ssd->lm;
    struct line *curline = NULL;

    curline = QTAILQ_FIRST(&lm->free_line_list);
    QTAILQ_REMOVE(&lm->free_line_list, curline, entry);
    lm->free_line_cnt--;

    /* wpp->curline is always our next-to-write super-block */
    wpp->curline = curline;
    wpp->ch = 0;
    wpp->lun = 0;
    wpp->pg = 0;
    wpp->blk = 0;
    wpp->pl = 0;
}

static inline void check_addr(int a, int max)
{
    ftl_assert(a >= 0 && a < max);
}

static struct line *get_next_free_line(struct ssd *ssd)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *curline = NULL;

    curline = QTAILQ_FIRST(&lm->free_line_list);
    if (!curline)
    {
        ftl_err("No free lines left in [%s] !!!!\n", ssd->ssdname);
        return NULL;
    }

    QTAILQ_REMOVE(&lm->free_line_list, curline, entry);
    lm->free_line_cnt--;
    return curline;
}

static void ssd_advance_write_pointer(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;
    struct write_pointer *wpp = &ssd->wp;
    struct line_mgmt *lm = &ssd->lm;

    check_addr(wpp->ch, spp->nchs);
    wpp->ch++;
    if (wpp->ch == spp->nchs)
    {
        wpp->ch = 0;
        check_addr(wpp->lun, spp->luns_per_ch);
        wpp->lun++;
        /* in this case, we should go to next lun */
        if (wpp->lun == spp->luns_per_ch)
        {
            wpp->lun = 0;
            /* go to next page in the block */
            check_addr(wpp->pg, spp->pgs_per_blk);
            wpp->pg++;
            if (wpp->pg == spp->pgs_per_blk)
            {
                wpp->pg = 0;
                /* move current line to {victim,full} line list */
                if (wpp->curline->vpc == spp->pgs_per_line)
                {
                    /* all pgs are still valid, move to full line list */
                    ftl_assert(wpp->curline->ipc == 0);
                    QTAILQ_INSERT_TAIL(&lm->full_line_list, wpp->curline, entry);
                    lm->full_line_cnt++;
                }
                else
                {
                    ftl_assert(wpp->curline->vpc >= 0 && wpp->curline->vpc < spp->pgs_per_line);
                    /* there must be some invalid pages in this line */
                    ftl_assert(wpp->curline->ipc > 0);
                    pqueue_insert(lm->victim_line_pq, wpp->curline);
                    lm->victim_line_cnt++;
                }
                /* current line is used up, pick another empty line */
                check_addr(wpp->blk, spp->blks_per_pl);
                wpp->curline = NULL;
                wpp->curline = get_next_free_line(ssd);
                if (!wpp->curline)
                {
                    /* TODO */
                    abort();
                }
                wpp->blk = wpp->curline->id;
                check_addr(wpp->blk, spp->blks_per_pl);
                /* make sure we are starting from page 0 in the super block */
                ftl_assert(wpp->pg == 0);
                ftl_assert(wpp->lun == 0);
                ftl_assert(wpp->ch == 0);
                /* TODO: assume # of pl_per_lun is 1, fix later */
                ftl_assert(wpp->pl == 0);
            }
        }
    }
}

static struct ppa get_new_page(struct ssd *ssd)
{
    struct write_pointer *wpp = &ssd->wp;
    struct ppa ppa;
    ppa.ppa = 0;
    ppa.g.ch = wpp->ch;
    ppa.g.lun = wpp->lun;
    ppa.g.pg = wpp->pg;
    ppa.g.blk = wpp->blk;
    ppa.g.pl = wpp->pl;
    ftl_assert(ppa.g.pl == 0);

    return ppa;
}

static void check_params(struct ssdparams *spp)
{
    /*
     * we are using a general write pointer increment method now, no need to
     * force luns_per_ch and nchs to be power of 2
     */

    // ftl_assert(is_power_of_2(spp->luns_per_ch));
    // ftl_assert(is_power_of_2(spp->nchs));
}

static void ssd_init_params(struct ssdparams *spp, FemuCtrl *n)
{
    spp->secsz = n->bb_params.secsz;             // 512
    spp->secs_per_pg = n->bb_params.secs_per_pg; // 8
    spp->pgs_per_blk = n->bb_params.pgs_per_blk; // 256
    spp->blks_per_pl = n->bb_params.blks_per_pl; /* 256 16GB */
    spp->pls_per_lun = n->bb_params.pls_per_lun; // 1
    spp->luns_per_ch = n->bb_params.luns_per_ch; // 8
    spp->nchs = n->bb_params.nchs;               // 8

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

    spp->pls_per_ch = spp->pls_per_lun * spp->luns_per_ch;
    spp->tt_pls = spp->pls_per_ch * spp->nchs;

    spp->tt_luns = spp->luns_per_ch * spp->nchs;

    /* line is special, put it at the end */
    spp->blks_per_line = spp->tt_luns; /* TODO: to fix under multiplanes */
    spp->pgs_per_line = spp->blks_per_line * spp->pgs_per_blk;
    spp->secs_per_line = spp->pgs_per_line * spp->secs_per_pg;
    spp->tt_lines = spp->blks_per_lun; /* TODO: to fix under multiplanes */

    spp->gc_thres_pcent = n->bb_params.gc_thres_pcent / 100.0;
    spp->gc_thres_lines = (int)((1 - spp->gc_thres_pcent) * spp->tt_lines);
    spp->gc_thres_pcent_high = n->bb_params.gc_thres_pcent_high / 100.0;
    spp->gc_thres_lines_high = (int)((1 - spp->gc_thres_pcent_high) * spp->tt_lines);
    spp->enable_gc_delay = true;

    /* CDFTL Number of entries*/
    spp->gtd_size = 3072;
    spp->cmt_size = 1024; // lpn
    spp->ctp_size = 32;   // page

    spp->cmt_bucket_size = 10;
    spp->ctp_bucket_size = 5;

    check_params(spp);
}

static void ssd_init_nand_page(struct nand_page *pg, struct ssdparams *spp)
{
    pg->nsecs = spp->secs_per_pg;
    pg->sec = g_malloc0(sizeof(nand_sec_status_t) * pg->nsecs);
    for (int i = 0; i < pg->nsecs; i++)
    {
        pg->sec[i] = SEC_FREE;
    }
    pg->status = PG_FREE;
}

static void ssd_init_nand_blk(struct nand_block *blk, struct ssdparams *spp)
{
    blk->npgs = spp->pgs_per_blk;
    blk->pg = g_malloc0(sizeof(struct nand_page) * blk->npgs);
    for (int i = 0; i < blk->npgs; i++)
    {
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
    for (int i = 0; i < pl->nblks; i++)
    {
        ssd_init_nand_blk(&pl->blk[i], spp);
    }
}

static void ssd_init_nand_lun(struct nand_lun *lun, struct ssdparams *spp)
{
    lun->npls = spp->pls_per_lun;
    lun->pl = g_malloc0(sizeof(struct nand_plane) * lun->npls);
    for (int i = 0; i < lun->npls; i++)
    {
        ssd_init_nand_plane(&lun->pl[i], spp);
    }
    lun->next_lun_avail_time = 0;
    lun->busy = false;
}

static void ssd_init_ch(struct ssd_channel *ch, struct ssdparams *spp)
{
    ch->nluns = spp->luns_per_ch;
    ch->lun = g_malloc0(sizeof(struct nand_lun) * ch->nluns);
    for (int i = 0; i < ch->nluns; i++)
    {
        ssd_init_nand_lun(&ch->lun[i], spp);
    }
    ch->next_ch_avail_time = 0;
    ch->busy = 0;
}

static void ssd_init_maptbl(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->maptbl = g_malloc0(sizeof(struct ppa) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++)
    {
        ssd->maptbl[i].ppa = UNMAPPED_PPA;
    }
}

static void ssd_init_rmap(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->rmap = g_malloc0(sizeof(uint64_t) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++)
    {
        ssd->rmap[i] = INVALID_LPN;
    }
}

static void ssd_init_cdftl(struct ssd *ssd, struct ssdparams *spp)
{

    /*  GTD  */
    ssd->gtd = g_malloc0(sizeof(struct gtd_entry) * spp->gtd_size);
    for (int i = 0; i < spp->gtd_size; i++)
    {
        ssd->gtd[i].tppn.ppa = UNMAPPED_PPA;
        ssd->gtd[i].location = 1; // Initially, all translation pages on flash
        ssd->gtd[i].dirty = 0;
    }

    /*  CMT  */
    ssd->cmt = g_malloc0(sizeof(struct cmt));
    ssd->cmt->max_entries = spp->cmt_size;
    ssd->cmt->current_size = 0;
    ssd->cmt->lru_head = NULL;
    ssd->cmt->lru_tail = NULL;

    ssd->cmt->hash_table_size = spp->cmt_bucket_size;
    ssd->cmt->hash_table = g_malloc0(sizeof(struct cmt_hash) * ssd->cmt->hash_table_size);
    for (int i = 0; i < ssd->cmt->hash_table_size; i++)
    {
        ssd->cmt->hash_table[i].hash_value = i;
        ssd->cmt->hash_table[i].cmt_entries = NULL;
        ssd->cmt->hash_table[i].hash_next = NULL;
    }

    /*  CTP   */
    ssd->ctp = g_malloc0(sizeof(struct ctp));
    ssd->ctp->max_entries = spp->ctp_size;
    ssd->ctp->current_size = 0;
    ssd->ctp->lru_head = NULL;
    ssd->ctp->lru_tail = NULL;

    ssd->ctp->hash_table_size = spp->ctp_bucket_size;
    ssd->ctp->hash_table = g_malloc0(sizeof(struct ctp_hash) * ssd->ctp->hash_table_size);
    for (int i = 0; i < ssd->ctp->hash_table_size; i++)
    {
        ssd->ctp->hash_table[i].hash_value = i;
        ssd->ctp->hash_table[i].ctp_entries = NULL;
        ssd->ctp->hash_table[i].hash_next = NULL;
    }

    /* Initialize Translation block */
    ssd->free_translation_blocks = 16;
    for (int i = 0; i < 16; i++)
    {
        ssd->translation_blocks[i].valid_pages = 0;
        ssd->translation_blocks[i].is_full = false;
        for (int j = 0; j < 256; j++)
        {
            struct translation_page *page = &ssd->translation_blocks[i].pages[j];
            page->mp = malloc(sizeof(struct map_page));
            page->mp->dppn = malloc(sizeof(struct ppa) * 512);
            for (int k = 0; k < 512; k++)
            {
                page->mp->dppn[k].ppa = UNMAPPED_PPA;
            }
            page->dirty = false;
        }
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
    for (int i = 0; i < spp->nchs; i++)
    {
        ssd_init_ch(&ssd->ch[i], spp);
    }

    /* initialize maptbl */
    ssd_init_maptbl(ssd);

    /* initialize rmap */
    ssd_init_rmap(ssd);

    /* initialize all the lines */
    ssd_init_lines(ssd);

    /* initialize write pointer, this is how we allocate new pages for writes */
    ssd_init_write_pointer(ssd);

    /* Iniitalize CDFTL data structures*/
    ssd_init_cdftl(ssd, spp);

    qemu_thread_create(&ssd->ftl_thread, "FEMU-FTL-Thread", ftl_thread, n, QEMU_THREAD_JOINABLE);
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

    if (ch >= 0 && ch < spp->nchs && lun >= 0 && lun < spp->luns_per_ch && pl >= 0 && pl < spp->pls_per_lun &&
        blk >= 0 && blk < spp->blks_per_pl && pg >= 0 && pg < spp->pgs_per_blk && sec >= 0 && sec < spp->secs_per_pg)
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

static inline struct nand_page *get_pg(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = get_blk(ssd, ppa);
    return &(blk->pg[ppa->g.pg]);
}

static uint64_t ssd_advance_status(struct ssd *ssd, struct ppa *ppa, struct nand_cmd *ncmd)
{
    int c = ncmd->cmd;
    uint64_t cmd_stime = (ncmd->stime == 0) ? qemu_clock_get_ns(QEMU_CLOCK_REALTIME) : ncmd->stime;
    uint64_t nand_stime;
    struct ssdparams *spp = &ssd->sp;
    struct nand_lun *lun = get_lun(ssd, ppa);
    uint64_t lat = 0;

    switch (c)
    {
    case NAND_READ:
        /* read: perform NAND cmd first */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : lun->next_lun_avail_time;
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
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : lun->next_lun_avail_time;
        if (ncmd->type == USER_IO)
        {
            lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;
        }
        else
        {
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
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->blk_er_lat;

        lat = lun->next_lun_avail_time - cmd_stime;
        break;

    default:
        ftl_err("Unsupported NAND command: 0x%x\n", c);
    }

    return lat;
}

/* update SSD status about one page from PG_VALID -> PG_VALID */
static void mark_page_invalid(struct ssd *ssd, struct ppa *ppa)
{
    struct line_mgmt *lm = &ssd->lm;
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    bool was_full_line = false;
    struct line *line;

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

    /* update corresponding line status */
    line = get_line(ssd, ppa);
    ftl_assert(line->ipc >= 0 && line->ipc < spp->pgs_per_line);
    if (line->vpc == spp->pgs_per_line)
    {
        ftl_assert(line->ipc == 0);
        was_full_line = true;
    }
    line->ipc++;
    ftl_assert(line->vpc > 0 && line->vpc <= spp->pgs_per_line);
    /* Adjust the position of the victime line in the pq under over-writes */
    if (line->pos)
    {
        /* Note that line->vpc will be updated by this call */
        pqueue_change_priority(lm->victim_line_pq, line->vpc - 1, line);
    }
    else
    {
        line->vpc--;
    }

    if (was_full_line)
    {
        /* move line: "full" -> "victim" */
        QTAILQ_REMOVE(&lm->full_line_list, line, entry);
        lm->full_line_cnt--;
        pqueue_insert(lm->victim_line_pq, line);
        lm->victim_line_cnt++;
    }
}

static void mark_page_valid(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    struct line *line;

    /* update page status */
    pg = get_pg(ssd, ppa);
    ftl_assert(pg->status == PG_FREE);
    pg->status = PG_VALID;

    /* update corresponding block status */
    blk = get_blk(ssd, ppa);
    ftl_assert(blk->vpc >= 0 && blk->vpc < ssd->sp.pgs_per_blk);
    blk->vpc++;

    /* update corresponding line status */
    line = get_line(ssd, ppa);
    ftl_assert(line->vpc >= 0 && line->vpc < ssd->sp.pgs_per_line);
    line->vpc++;
}

static void mark_block_free(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = get_blk(ssd, ppa);
    struct nand_page *pg = NULL;

    for (int i = 0; i < spp->pgs_per_blk; i++)
    {
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
    if (ssd->sp.enable_gc_delay)
    {
        struct nand_cmd gcr;
        gcr.type = GC_IO;
        gcr.cmd = NAND_READ;
        gcr.stime = 0;
        ssd_advance_status(ssd, ppa, &gcr);
    }
}

/* move valid page data (already in DRAM) from victim line to a new page */
static uint64_t gc_write_page(struct ssd *ssd, struct ppa *old_ppa)
{
    struct ppa new_ppa;
    struct nand_lun *new_lun;
    uint64_t lpn = get_rmap_ent(ssd, old_ppa);

    ftl_assert(valid_lpn(ssd, lpn));
    new_ppa = get_new_page(ssd);
    /* update maptbl */
    set_maptbl_ent(ssd, lpn, &new_ppa);
    /* update rmap */
    set_rmap_ent(ssd, lpn, &new_ppa);

    mark_page_valid(ssd, &new_ppa);

    /* need to advance the write pointer here */
    ssd_advance_write_pointer(ssd);

    if (ssd->sp.enable_gc_delay)
    {
        struct nand_cmd gcw;
        gcw.type = GC_IO;
        gcw.cmd = NAND_WRITE;
        gcw.stime = 0;
        ssd_advance_status(ssd, &new_ppa, &gcw);
    }

    /* advance per-ch gc_endtime as well */
#if 0
    new_ch = get_ch(ssd, &new_ppa);
    new_ch->gc_endtime = new_ch->next_ch_avail_time;
#endif

    new_lun = get_lun(ssd, &new_ppa);
    new_lun->gc_endtime = new_lun->next_lun_avail_time;

    return 0;
}

static struct line *select_victim_line(struct ssd *ssd, bool force)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *victim_line = NULL;

    victim_line = pqueue_peek(lm->victim_line_pq);
    if (!victim_line)
    {
        return NULL;
    }

    if (!force && victim_line->ipc < ssd->sp.pgs_per_line / 8)
    {
        return NULL;
    }

    pqueue_pop(lm->victim_line_pq);
    victim_line->pos = 0;
    lm->victim_line_cnt--;

    /* victim_line is a danggling node now */
    return victim_line;
}

/* here ppa identifies the block we want to clean */
static void clean_one_block(struct ssd *ssd, struct ppa *ppa, FemuCtrl *n)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_page *pg_iter = NULL;
    int cnt = 0;

    // waf
    uint64_t page_size = spp->secs_per_pg * spp->secsz;

    for (int pg = 0; pg < spp->pgs_per_blk; pg++)
    {
        ppa->g.pg = pg;
        pg_iter = get_pg(ssd, ppa);
        /* there shouldn't be any free page in victim blocks */
        ftl_assert(pg_iter->status != PG_FREE);
        if (pg_iter->status == PG_VALID)
        {
            gc_read_page(ssd, ppa);
            /* delay the maptbl update until "write" happens */
            gc_write_page(ssd, ppa);
            cnt++;
            n->bytes_written_gc += page_size;
        }
    }

    ftl_assert(get_blk(ssd, ppa)->vpc == cnt);
}

static void mark_line_free(struct ssd *ssd, struct ppa *ppa)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *line = get_line(ssd, ppa);
    line->ipc = 0;
    line->vpc = 0;
    /* move this line to free line list */
    QTAILQ_INSERT_TAIL(&lm->free_line_list, line, entry);
    lm->free_line_cnt++;
}

static int do_gc(struct ssd *ssd, bool force, FemuCtrl *n)
{
    struct line *victim_line = NULL;
    struct ssdparams *spp = &ssd->sp;
    struct nand_lun *lunp;
    struct ppa ppa;
    int ch, lun;

    victim_line = select_victim_line(ssd, force);
    if (!victim_line)
    {
        return -1;
    }

    ppa.g.blk = victim_line->id;
    ftl_debug("GC-ing line:%d,ipc=%d,victim=%d,full=%d,free=%d\n", ppa.g.blk, victim_line->ipc, ssd->lm.victim_line_cnt,
              ssd->lm.full_line_cnt, ssd->lm.free_line_cnt);

    /* copy back valid data */
    for (ch = 0; ch < spp->nchs; ch++)
    {
        for (lun = 0; lun < spp->luns_per_ch; lun++)
        {
            ppa.g.ch = ch;
            ppa.g.lun = lun;
            ppa.g.pl = 0;
            lunp = get_lun(ssd, &ppa);
            clean_one_block(ssd, &ppa, n);
            mark_block_free(ssd, &ppa);

            if (spp->enable_gc_delay)
            {
                struct nand_cmd gce;
                gce.type = GC_IO;
                gce.cmd = NAND_ERASE;
                gce.stime = 0;
                ssd_advance_status(ssd, &ppa, &gce);
            }

            lunp->gc_endtime = lunp->next_lun_avail_time;
        }
    }

    /* update line status */
    mark_line_free(ssd, &ppa);

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

    if (end_lpn >= spp->tt_pgs)
    {
        ftl_err("start_lpn=%" PRIu64 ",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
    }

    /* normal IO read path */
    for (lpn = start_lpn; lpn <= end_lpn; lpn++)
    {
        ppa = get_maptbl_ent(ssd, lpn);
        if (!mapped_ppa(&ppa) || !valid_ppa(ssd, &ppa))
        {
            // printf("%s,lpn(%" PRId64 ") not mapped to valid ppa\n", ssd->ssdname, lpn);
            // printf("Invalid ppa,ch:%d,lun:%d,blk:%d,pl:%d,pg:%d,sec:%d\n",
            // ppa.g.ch, ppa.g.lun, ppa.g.blk, ppa.g.pl, ppa.g.pg, ppa.g.sec);
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

static uint64_t ssd_write(struct ssd *ssd, NvmeRequest *req, FemuCtrl *n)
{
    uint64_t lba = req->slba;
    struct ssdparams *spp = &ssd->sp;
    int len = req->nlb;
    uint64_t start_lpn = lba / spp->secs_per_pg;
    uint64_t end_lpn = (lba + len - 1) / spp->secs_per_pg;
    struct ppa ppa;
    uint64_t lpn;
    uint64_t curlat = 0, maxlat = 0;
    int r;

    if (end_lpn >= spp->tt_pgs)
    {
        ftl_err("start_lpn=%" PRIu64 ",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
    }

    // waf
    n->bytes_written_host += len * spp->secsz;

    while (should_gc_high(ssd))
    {
        /* perform GC here until !should_gc(ssd) */
        r = do_gc(ssd, true, n);
        if (r == -1)
            break;
    }

    for (lpn = start_lpn; lpn <= end_lpn; lpn++)
    {
        ppa = get_maptbl_ent(ssd, lpn);
        if (mapped_ppa(&ppa))
        {
            /* update old page information first */
            mark_page_invalid(ssd, &ppa);
            set_rmap_ent(ssd, INVALID_LPN, &ppa);
        }

        // UNMAPPED PPA
        // Get a new and real ppa

        /* new write */
        ppa = get_new_page(ssd);
        /* update maptbl */
        set_maptbl_ent(ssd, lpn, &ppa);
        /* update rmap */
        set_rmap_ent(ssd, lpn, &ppa);

        mark_page_valid(ssd, &ppa);

        /* need to advance the write pointer here */
        ssd_advance_write_pointer(ssd);

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

    while (!*(ssd->dataplane_started_ptr))
    {
        usleep(100000);
    }

    /* FIXME: not safe, to handle ->to_ftl and ->to_poller gracefully */
    ssd->to_ftl = n->to_ftl;
    ssd->to_poller = n->to_poller;

    while (1)
    {
        for (i = 1; i <= n->nr_pollers; i++)
        {
            if (!ssd->to_ftl[i] || !femu_ring_count(ssd->to_ftl[i]))
                continue;

            rc = femu_ring_dequeue(ssd->to_ftl[i], (void *)&req, 1);
            if (rc != 1)
            {
                printf("FEMU: FTL to_ftl dequeue failed\n");
            }

            ftl_assert(req);
            switch (req->cmd.opcode)
            {
            case NVME_CMD_WRITE:
                lat = ssd_write(ssd, req, n);
                break;
            case NVME_CMD_READ:
                lat = ssd_read(ssd, req);
                break;
            case NVME_CMD_DSM:
                lat = 0;
                break;
            default:
                // ftl_err("FTL received unkown request type, ERROR\n");
                ;
            }

            req->reqlat = lat;
            req->expire_time += lat;

            rc = femu_ring_enqueue(ssd->to_poller[i], (void *)&req, 1);
            if (rc != 1)
            {
                ftl_err("FTL to_poller enqueue failed\n");
            }

            /* clean one line if needed (in the background) */
            if (should_gc(ssd))
            {
                do_gc(ssd, false, n);
            }
        }
    }

    return NULL;
}
