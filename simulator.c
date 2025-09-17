#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <ctype.h>

/* ---------------- CONFIGURATION ---------------- */
#define VIRT_ADDR_BITS 32
#define PAGE_SZ 4096U
#define PAGE_OFFSET_BITS 12
#define PHYS_MEM_SZ (64 * 1024)
#define NUM_PHY_FRAMES (PHYS_MEM_SZ / PAGE_SZ)
#define TLB_SIZE 16
#define CACHE_SZ (8 * 1024)
#define BLOCK_SZ 64
#define CACHE_WAYS 2

#define NUM_PAGES (1U << (VIRT_ADDR_BITS - PAGE_OFFSET_BITS))
#define NUM_CACHE_BLOCKS (CACHE_SZ / BLOCK_SZ)
#define NUM_CACHE_SETS (NUM_CACHE_BLOCKS / CACHE_WAYS)
#define CACHE_SET_BITS (__builtin_ctz(NUM_CACHE_SETS))
#define BLOCK_OFFSET_BITS (__builtin_ctz(BLOCK_SZ))

/* ---------------- Data Structures ---------------- */
typedef uint32_t vaddr_t;
typedef uint32_t paddr_t;
typedef uint32_t vpn_t;
typedef uint32_t pfn_t;

typedef struct { int valid; pfn_t frame_num; uint64_t last_used; } page_entry_t;
typedef struct { int valid; vpn_t vpn; pfn_t frame_num; uint64_t last_used; } tlb_entry_sim_t;
typedef struct { int occupied; vpn_t vpn; uint64_t last_used; } frame_info_t;
typedef struct { int valid; uint32_t tag; uint64_t last_used; } cache_line_sim_t;
typedef struct { cache_line_sim_t *lines; } cache_set_sim_t;

/* ---------------- Globals ---------------- */
static page_entry_t *page_table_sim = NULL;
static tlb_entry_sim_t tlb_sim[TLB_SIZE];
static frame_info_t frames_sim[NUM_PHY_FRAMES];
static uint8_t *phys_mem_sim = NULL;
static cache_set_sim_t *cache_sim = NULL;

static uint64_t stat_total_accesses = 0, stat_tlb_hits = 0, stat_tlb_misses = 0;
static uint64_t stat_page_faults = 0, stat_page_replacements = 0;
static uint64_t stat_cache_hits = 0, stat_cache_misses = 0;
static uint64_t sim_time = 1;

/* ---------------- Utility Functions ---------------- */
static uint64_t current_time() { return sim_time++; }

static int find_lru(uint64_t *arr, int n) {
    uint64_t min_val = (uint64_t)-1;
    int idx = 0;
    for (int i = 0; i < n; i++) if (arr[i] < min_val) { min_val = arr[i]; idx = i; }
    return idx;
}

/* ---------------- TLB Operations ---------------- */
static void tlb_reset() { for (int i = 0; i < TLB_SIZE; i++) tlb_sim[i].valid = 0; }

static int tlb_lookup_sim(vpn_t vpn, pfn_t *out_frame) {
    for (int i = 0; i < TLB_SIZE; i++) {
        if (tlb_sim[i].valid && tlb_sim[i].vpn == vpn) {
            tlb_sim[i].last_used = current_time();
            *out_frame = tlb_sim[i].frame_num;
            stat_tlb_hits++;
            return 1;
        }
    }
    stat_tlb_misses++;
    return 0;
}

// Add entry to TLB, evict LRU if needed
static void tlb_add(vpn_t vpn, pfn_t frame) {
    int free_idx = -1; uint64_t times[TLB_SIZE];
    for (int i = 0; i < TLB_SIZE; i++) {
        times[i] = tlb_sim[i].last_used;
        if (!tlb_sim[i].valid && free_idx == -1) free_idx = i;
    }
    int idx = (free_idx != -1) ? free_idx : find_lru(times, TLB_SIZE);
    tlb_sim[idx].valid = 1; tlb_sim[idx].vpn = vpn; tlb_sim[idx].frame_num = frame;
    tlb_sim[idx].last_used = current_time();
}

/* ---------------- Page Table & Frames ---------------- */
static void page_table_init_sim() { page_table_sim = calloc(NUM_PAGES, sizeof(page_entry_t)); }

static void frames_init_sim() { for (int i = 0; i < NUM_PHY_FRAMES; i++) frames_sim[i].occupied = 0; }

// Allocate a free frame or evict LRU frame
static int allocate_frame_sim(vpn_t vpn) {
    for (int i = 0; i < NUM_PHY_FRAMES; i++) if (!frames_sim[i].occupied) {
        frames_sim[i].occupied = 1; frames_sim[i].vpn = vpn; frames_sim[i].last_used = current_time(); return i;
    }
    uint64_t times[NUM_PHY_FRAMES]; for (int i = 0; i < NUM_PHY_FRAMES; i++) times[i] = frames_sim[i].last_used;
    int evict_idx = find_lru(times, NUM_PHY_FRAMES);
    vpn_t old_vpn = frames_sim[evict_idx].vpn;
    if (page_table_sim[old_vpn].valid) { page_table_sim[old_vpn].valid = 0; stat_page_replacements++; }
    frames_sim[evict_idx].vpn = vpn; frames_sim[evict_idx].last_used = current_time();
    return evict_idx;
}

// Handle page fault
static pfn_t handle_page_fault_sim(vpn_t vpn) {
    stat_page_faults++; int frame = allocate_frame_sim(vpn);
    page_table_sim[vpn].valid = 1; page_table_sim[vpn].frame_num = frame; page_table_sim[vpn].last_used = current_time();
    memset(phys_mem_sim + (frame * PAGE_SZ), 0, PAGE_SZ);
    return frame;
}

// Lookup page in page table
static pfn_t page_lookup_sim(vpn_t vpn) {
    if (page_table_sim[vpn].valid) { page_table_sim[vpn].last_used = current_time(); frames_sim[page_table_sim[vpn].frame_num].last_used = current_time(); return page_table_sim[vpn].frame_num; }
    return handle_page_fault_sim(vpn);
}

/* ---------------- Cache Operations ---------------- */
static void cache_init_sim() {
    cache_sim = calloc(NUM_CACHE_SETS, sizeof(cache_set_sim_t));
    for (int i = 0; i < NUM_CACHE_SETS; i++) cache_sim[i].lines = calloc(CACHE_WAYS, sizeof(cache_line_sim_t));
}

// Access cache (return 1 if hit, 0 if miss)
static int cache_access_sim(paddr_t paddr) {
    uint32_t block_addr = paddr >> BLOCK_OFFSET_BITS;
    uint32_t set_idx = block_addr & (NUM_CACHE_SETS - 1);
    uint32_t tag = block_addr >> CACHE_SET_BITS;
    cache_set_sim_t *set = &cache_sim[set_idx];

    for (int i = 0; i < CACHE_WAYS; i++) if (set->lines[i].valid && set->lines[i].tag == tag) { set->lines[i].last_used = current_time(); stat_cache_hits++; return 1; }

    stat_cache_misses++;
    int free_idx = -1; uint64_t times[CACHE_WAYS];
    for (int i = 0; i < CACHE_WAYS; i++) { times[i] = set->lines[i].last_used; if (!set->lines[i].valid && free_idx == -1) free_idx = i; }
    int idx = (free_idx != -1) ? free_idx : find_lru(times, CACHE_WAYS);
    set->lines[idx].valid = 1; set->lines[idx].tag = tag; set->lines[idx].last_used = current_time();
    return 0;
}

/* ---------------- Address Handling ---------------- */
static void read_address_sim(vaddr_t vaddr, int verbose) {
    stat_total_accesses++;
    vpn_t vpn = vaddr >> PAGE_OFFSET_BITS;
    uint32_t offset = vaddr & (PAGE_SZ - 1);
    pfn_t frame;

    int hit = tlb_lookup_sim(vpn, &frame);
    if (!hit) { frame = page_lookup_sim(vpn); tlb_add(vpn, frame); }

    paddr_t paddr = ((paddr_t)frame << PAGE_OFFSET_BITS) | offset;
    int cache_hit = cache_access_sim(paddr);

    if (verbose) printf("R 0x%08x -> VPN=%u PFN=%u PADDR=0x%08x Cache:%s TLB:%s\n", vaddr, vpn, frame, paddr, cache_hit ? "HIT" : "MISS", hit ? "HIT" : "MISS");
}

/* ---------------- Initialization & Cleanup ---------------- */
static void sim_init() {
    phys_mem_sim = calloc(PHYS_MEM_SZ, 1); tlb_reset(); page_table_init_sim(); frames_init_sim(); cache_init_sim();
}

static void sim_cleanup() {
    if (page_table_sim) free(page_table_sim);
    if (phys_mem_sim) free(phys_mem_sim);
    if (cache_sim) { for (int i = 0; i < NUM_CACHE_SETS; i++) free(cache_sim[i].lines); free(cache_sim); }
}

/* ---------------- Main Function ---------------- */
static int parse_addr(const char *s, vaddr_t *out) {
    while (isspace((unsigned char)*s)) ++s;
    unsigned long val = (s[0]=='0' && (s[1]=='x'||s[1]=='X')) ? strtoul(s,NULL,16) : strtoul(s,NULL,10);
    *out = (vaddr_t)val;
    return 1;
}

int main(int argc, char **argv) {
    FILE *file = stdin; int verbose = 0;
    if (argc >= 2) { file = fopen(argv[1], "r"); if (!file) { perror("fopen"); return 1; } }
    if (argc >= 3 && strcmp(argv[2], "-v") == 0) verbose = 1;
    if ((NUM_CACHE_SETS & (NUM_CACHE_SETS-1)) != 0) { fprintf(stderr,"Cache sets must be power of two\n"); return 1; }

    sim_init();

    char line[256];
    while (fgets(line,sizeof(line),file)) {
        char *p = line; while (isspace((unsigned char)*p)) ++p;
        if (*p=='\0'||*p=='#') continue;
        if (*p=='R'||*p=='r') { p++; while(isspace((unsigned char)*p)) ++p; vaddr_t addr; if(parse_addr(p,&addr)) read_address_sim(addr,verbose);}
        else if (*p=='V'||*p=='v') verbose=1;
        else if (*p=='S'||*p=='s') {
            printf("STAT: accesses=%" PRIu64 " tlb_hits=%" PRIu64 " tlb_misses=%" PRIu64
                   " page_faults=%" PRIu64 " cache_hits=%" PRIu64 " cache_misses=%" PRIu64 "\n",
                   stat_total_accesses, stat_tlb_hits, stat_tlb_misses, stat_page_faults, stat_cache_hits, stat_cache_misses);
        }
    }

    printf("\n--- Simulation Summary ---\n");
    printf("Total memory accesses: %" PRIu64 "\n", stat_total_accesses);
    printf("TLB hits: %" PRIu64 "  misses: %" PRIu64 "\n", stat_tlb_hits, stat_tlb_misses);
    printf("Page faults: %" PRIu64 "  replacements: %" PRIu64 "\n", stat_page_faults, stat_page_replacements);
    printf("Cache hits: %" PRIu64 "  misses: %" PRIu64 "\n", stat_cache_hits, stat_cache_misses);

    sim_cleanup();
    if(file!=stdin) fclose(file);
    return 0;
}
