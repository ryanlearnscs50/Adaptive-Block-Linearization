#include <iostream>
#include <vector>
#include <unordered_map>
#include <map>
#include <list>
#include <algorithm>
#include <chrono>
#include <iomanip>
#include <cmath>
#include <numeric>
#include <random>

using namespace std;

// ==========================================
// CONFIGURATION & CONSTANTS
// ==========================================
const int BLOCK_SIZE = 4096;
const int CACHE_SIZE = 32 * 1024; // 32KB L1 Cache
const int CACHE_LINE = 64;        // 64 Byte Cache Lines
const int WAYS = 8;               // 8-Way Associativity
const int SETS = CACHE_SIZE / (CACHE_LINE * WAYS);
const int PAGE_SIZE = 4096;

struct Item { int weight; int value; };
vector<Item> items;

// ==========================================
// PART 1: CACHE & TLB SIMULATOR
// ==========================================
struct CacheLine { long long tag; };
struct Set { list<CacheLine> lines; };
struct TLBEntry { long long page_id; };

Set l1_cache[SETS];
list<TLBEntry> tlb;
long long total_refs = 0;
long long l1_misses = 0;
long long tlb_misses = 0;

void access_memory(long long addr) {
    total_refs++;

    // TLB Simulation (Fully Associative, 64 Entries)
    long long page_id = addr / PAGE_SIZE;
    bool tlb_hit = false;
    for(auto it = tlb.begin(); it != tlb.end(); ++it) {
        if(it->page_id == page_id) {
            tlb_hit = true;
            tlb.splice(tlb.begin(), tlb, it); // LRU Update
            break;
        }
    }
    if(!tlb_hit) {
        tlb_misses++;
        if(tlb.size() >= 64) tlb.pop_back();
        tlb.push_front({page_id});
    }

    // L1 Cache Simulation (Set Associative)
    long long set_index = (addr / CACHE_LINE) % SETS;
    long long tag = (addr / CACHE_LINE) / SETS;
    
    bool cache_hit = false;
    auto& lines = l1_cache[set_index].lines;
    for(auto it = lines.begin(); it != lines.end(); ++it) {
        if(it->tag == tag) {
            cache_hit = true;
            lines.splice(lines.begin(), lines, it); // LRU Update
            break;
        }
    }
    if(!cache_hit) {
        l1_misses++;
        if(lines.size() >= WAYS) lines.pop_back();
        lines.push_front({tag});
    }
}

void reset_hardware() {
    total_refs = 0; l1_misses = 0; tlb_misses = 0;
    tlb.clear();
    for(int i=0; i<SETS; i++) l1_cache[i].lines.clear();
}

// ==========================================
// PART 2: SOLVERS
// ==========================================

// 2.1 Block-Adaptive Linearization (BAL)
struct BALSolver {
    unordered_map<long long, vector<long long>> blocks;
    long long HEAP_BASE = 0x10000000; // Simulated Heap Start

    long long& access(int idx, int capacity, int max_w, bool sim_cache) {
        long long global_index = ((long long)idx * max_w) + capacity;
        long long block_id = global_index / BLOCK_SIZE;
        int offset = global_index % BLOCK_SIZE;
        
        if (sim_cache) {
            // Address = Base + BlockOffset + ElementOffset * 8 bytes
            long long addr = HEAP_BASE + (block_id * BLOCK_SIZE * 8) + (offset * 8);
            access_memory(addr);
        }

        if (blocks.find(block_id) == blocks.end()) {
            blocks[block_id] = vector<long long>(BLOCK_SIZE, -1);
        }
        return blocks[block_id][offset];
    }

    long long solve(int idx, int capacity, int max_w, bool sim_cache = false) {
        if (idx == items.size() || capacity == 0) return 0;
        
        long long& mem = access(idx, capacity, max_w, sim_cache);
        if (mem != -1) return mem;
        
        long long res;
        if (items[idx].weight > capacity) res = solve(idx + 1, capacity, max_w, sim_cache);
        else res = max(solve(idx + 1, capacity, max_w, sim_cache), 
                      items[idx].value + solve(idx + 1, capacity - items[idx].weight, max_w, sim_cache));
        return mem = res;
    }
};

// 2.2 Meet-in-the-Middle (MitM)
struct MitMSolver {
    void generate(int start, int end, vector<pair<long long, long long>>& out, int limit_w) {
        int range = end - start;
        int psize = 1 << range;
        for (int i = 0; i < psize; i++) {
            long long w = 0, v = 0;
            for (int j = 0; j < range; j++) {
                if (i & (1 << j)) { w += items[start + j].weight; v += items[start + j].value; }
            }
            if (w <= limit_w) out.push_back({w, v});
        }
    }

    long long solve(int cap) {
        int mid = items.size() / 2;
        vector<pair<long long, long long>> L, R;
        generate(0, mid, L, cap);
        generate(mid, items.size(), R, cap);
        
        sort(L.begin(), L.end());
        vector<pair<long long, long long>> L_clean;
        long long max_v = -1;
        for(auto& p : L) { 
            if(p.second > max_v) { max_v = p.second; L_clean.push_back(p); } 
        }
        
        long long global_max = 0;
        long long INF_VAL = 2000000000000000000LL; 
        
        for(auto& r : R) {
            long long rem = cap - r.first;
            auto it = upper_bound(L_clean.begin(), L_clean.end(), make_pair(rem, INF_VAL));
            if (it != L_clean.begin()) global_max = max(global_max, r.second + prev(it)->second);
            else global_max = max(global_max, r.second);
        }
        return global_max;
    }
};

// 2.3 Standard Map
struct MapSolver {
    map<long long, long long> memo;
    long long solve(int idx, int capacity, bool sim_cache = false) {
        if (idx == items.size() || capacity == 0) return 0;
        long long key = ((long long)idx << 32) | capacity;
        
        if (sim_cache) {
            // Simulate tree traversal (approx 18 pointer jumps for size 200k)
            for(int i=0; i<18; i++) access_memory(rand() * 8); 
        }

        if (memo.count(key)) return memo[key];
        
        long long res;
        if (items[idx].weight > capacity) res = solve(idx + 1, capacity, sim_cache);
        else res = max(solve(idx + 1, capacity, sim_cache), 
                      items[idx].value + solve(idx + 1, capacity - items[idx].weight, sim_cache));
        return memo[key] = res;
    }
};

// ==========================================
// PART 3: EXPERIMENT RUNNER
// ==========================================
int main() {
    srand(42);
    cout << fixed << setprecision(4);

    // --- EXP 1: CAPACITY SCALING ---
    cout << "\n=== EXPERIMENT 1: CAPACITY SCALING (N=34) ===" << endl;
    cout << "W         | BAL (s)  | MitM (s)" << endl;
    vector<int> weights = {2000, 20000, 200000, 2000000};
    for(int W : weights) {
        items.clear();
        for(int i=0; i<34; i++) items.push_back({rand()%1000+1, rand()%1000+1});
        
        // BAL
        auto start = chrono::high_resolution_clock::now();
        BALSolver bal; bal.solve(0, W, W);
        double t_bal = chrono::duration<double>(chrono::high_resolution_clock::now() - start).count();

        // MitM
        start = chrono::high_resolution_clock::now();
        MitMSolver mitm; mitm.solve(W);
        double t_mitm = chrono::duration<double>(chrono::high_resolution_clock::now() - start).count();

        cout << left << setw(10) << W << "| " << t_bal << "   | " << t_mitm << endl;
    }

    // --- EXP 2: SCALABILITY ---
    cout << "\n=== EXPERIMENT 2: SCALABILITY (W=1M) ===" << endl;
    cout << "N   | BAL (s)  | MitM (s)" << endl;
    vector<int> ns = {20, 26, 32, 38, 44};
    for(int n : ns) {
        items.clear();
        for(int i=0; i<n; i++) items.push_back({rand()%1000+1, rand()%1000+1});
        int W = 1000000;

        auto start = chrono::high_resolution_clock::now();
        BALSolver bal; bal.solve(0, W, W);
        double t_bal = chrono::duration<double>(chrono::high_resolution_clock::now() - start).count();

        double t_mitm = 0;
        if(n <= 44) {
            start = chrono::high_resolution_clock::now();
            MitMSolver mitm; mitm.solve(W);
            t_mitm = chrono::duration<double>(chrono::high_resolution_clock::now() - start).count();
        }
        cout << left << setw(4) << n << "| " << t_bal << "   | " << t_mitm << endl;
    }

    // --- EXP 3: DENSITY ---
    cout << "\n=== EXPERIMENT 3: DENSITY (N=34, W=100k) ===" << endl;
    cout << "Range | BAL (s)  | Map (s)" << endl;
    vector<int> ranges = {10, 100, 1000, 10000};
    for(int R : ranges) {
        items.clear();
        for(int i=0; i<34; i++) items.push_back({rand()%R+1, rand()%100+1});
        int W = 100000;

        auto s = chrono::high_resolution_clock::now();
        BALSolver bal; bal.solve(0, W, W);
        double t_bal = chrono::duration<double>(chrono::high_resolution_clock::now() - s).count();

        s = chrono::high_resolution_clock::now();
        MapSolver map; map.solve(0, W);
        double t_map = chrono::duration<double>(chrono::high_resolution_clock::now() - s).count();

        cout << left << setw(6) << R << "| " << t_bal << "   | " << t_map << endl;
    }

    // --- EXP 4: CACHE SIMULATION ---
    cout << "\n=== EXPERIMENT 4: CACHE SIMULATION (N=34, W=500k) ===" << endl;
    items.clear();
    for(int i=0; i<34; i++) items.push_back({rand()%1000+1, rand()%1000+1});
    
    reset_hardware();
    BALSolver bal_sim;
    bal_sim.solve(0, 500000, 500000, true);
    cout << "BAL L1 Miss Rate: " << (double)l1_misses/total_refs*100.0 << "%" << endl;
    cout << "BAL TLB Misses:   " << tlb_misses << endl;

    reset_hardware();
    MapSolver map_sim;
    map_sim.solve(0, 500000, true);
    cout << "Map L1 Miss Rate: " << (double)l1_misses/total_refs*100.0 << "%" << endl;
    cout << "Map TLB Misses:   " << tlb_misses << endl;

    return 0;
}