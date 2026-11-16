/*
 * ============================================================================
 *   URBAN TRAFFIC SIGNAL COORDINATOR
 *   Challenge 6 : Network Throughput Optimisation using Maximum Flow
 *   Subject     : Design and Analysis of Algorithms (DAA) - PBL Project
 * ============================================================================
 *
 *   TEAM
 *   ----
 *   1. Sanskriti              (590022775)  -> COMPONENT 1  Data Ingestion and Validation
 *   2. Radhika Mehrotra       (590025253)  -> COMPONENT 2  Graph Model Builder
 *   3. Anshul Bartwal         (590027937)  -> COMPONENT 3  Maximum Flow Engine
 *   4. Vedansh Singh          (590022205)  -> COMPONENT 4  Baseline and Benchmarking
 *   5. Dhruv Pratap Chauhan   (590023965)  -> COMPONENT 5  Explanation and Reporting Layer
 *                                          -> COMPONENT 6  Testing and Evaluation Suite
 *      (5 members, 6 components, so member 5 has two. Change it if your
 *       team divided it differently.)
 *
 *   HOW TO COMPILE AND RUN
 *   ----------------------
 *       gcc traffic_coord.c -o traffic -O2
 *       ./traffic              (on Windows:  traffic.exe)
 *
 *   FILE LAYOUT (search for the "COMPONENT" banners)
 *   ------------------------------------------------
 *       SHARED      constants, structs, helper functions used by everybody
 *       COMPONENT 1 Sanskriti       load CSV, validate, clean, make datasets
 *       COMPONENT 2 Radhika         dataset -> flow network (super source/sink)
 *       COMPONENT 3 Anshul          Edmonds-Karp, min cut, invariant checker
 *       COMPONENT 4 Vedansh         DFS Ford-Fulkerson, greedy, brute force, timing
 *       COMPONENT 5 Dhruv           screens, officer report, advice
 *       COMPONENT 6 Dhruv           test suite
 *       MAIN        menu loop that connects everything
 *
 *   DAA CONCEPTS USED (and where)
 *   -----------------------------
 *       Graph algorithms + BFS ............. Component 3  bfs_find_path()
 *       Greedy strategy (shortest path) .... Component 3  edmonds_karp(), Component 4 greedy_shortest_path()
 *       Residual graph + loop invariants ... Component 3  apply_path(), check_constraints()
 *       Max flow min cut duality ........... Component 3  reachable_from_source(), min_cut_value()
 *       Asymptotic analysis O(VE^2) ........ Component 4  complexity_check()
 *       Brute force (exhaustive search) .... Component 4  brute_force_min_cut()
 *       Algorithm selection ................ Component 5  report_officer() (Dinic / min cost flow note)
 * ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <limits.h>
#include <errno.h>

#ifdef _WIN32
  #include <windows.h>
  #ifndef ENABLE_VIRTUAL_TERMINAL_PROCESSING
    #define ENABLE_VIRTUAL_TERMINAL_PROCESSING 0x0004
  #endif
#else
  #include <time.h>
#endif


/* ============================================================================
 *   SHARED SECTION  (constants, structs, small helpers)
 * ========================================================================== */

#define NAME_LEN         24            /* max junction name length          */
#define FIELD_LEN        16            /* max length of id / type / status  */
#define LOG_MAX          300           /* max lines kept in cleaning log    */
#define LOG_LEN          110
#define INF_CAP          1000000000000000LL   /* "infinite" capacity = 1e15 */
#define MAX_CAP          1000000000LL         /* largest capacity accepted  */
#define BRUTE_MAX_NODES  20            /* brute force only up to 2^20 cuts  */
#define TRACE_LIMIT      30            /* augmentations printed in a trace  */
#define LINE_W           70

/* ---- one road segment (one valid record of the CSV) ---- */
typedef struct {
    char id[FIELD_LEN];
    int  from, to;                     /* junction numbers                  */
    long long cap;                     /* vehicles per minute               */
    char window[FIELD_LEN];            /* time window                       */
    char type[FIELD_LEN];              /* road type                         */
    char status[FIELD_LEN];            /* open / closed / incident          */
} Road;

/* ---- the cleaned dataset (output of Component 1) ---- */
typedef struct {
    char (*names)[NAME_LEN];  int nNodes, capNodes;
    Road *roads;              int nRoads, capRoads;
    int       *entryNode;
    long long *entryDemand;   int nEntry, capEntry;
    int       *exitNode;      int nExit,  capExit;

    /* cleaning report numbers */
    int linesRead, accepted, rejected, merged, closedRoads;
    char log[LOG_MAX][LOG_LEN];
    int  nLog, logDropped;
    char source[80];
} Dataset;

/* ---- the flow network (output of Component 2) ---- */
typedef struct {
    const Dataset *ds;
    int n, m;                          /* nodes (incl. S,T), edge slots     */
    int S, T, nReal;                   /* super source, super sink, junctions */
    int *from, *to, *roadIdx;          /* per edge slot                     */
    long long *cap;                    /* residual capacity c_f             */
    long long *orig;                   /* original capacity c               */
    int *adjStart, *adj;               /* adjacency lists (CSR style)       */
} Graph;

/* ---- operation counters (Component 3 fills, Component 4 compares) ---- */
typedef struct {
    long long searches;                /* BFS / DFS runs                    */
    long long augmentations;
    long long relaxations;             /* edges examined while searching    */
} Counters;

static int g_trace = 0;                /* 1 = print each augmenting path    */
static int useColor = 1;               /* grey / white / black theme        */

#define GROW(p, n, cap) do { \
    if ((n) >= (cap)) { \
        (cap) = (cap) ? (cap) * 2 : 16; \
        (p) = realloc((p), (size_t)(cap) * sizeof(*(p))); \
        if (!(p)) { puts("Out of memory."); exit(1); } \
    } } while (0)

static void *xmalloc(size_t sz) {
    void *p = malloc(sz ? sz : 1);
    if (!p) { puts("Out of memory."); exit(1); }
    return p;
}
static void *xcalloc(size_t n, size_t sz) {
    void *p = calloc(n ? n : 1, sz ? sz : 1);
    if (!p) { puts("Out of memory."); exit(1); }
    return p;
}

/* high resolution timer in milliseconds */
#ifdef _WIN32
static double now_ms(void) {
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return 1000.0 * (double)c.QuadPart / (double)f.QuadPart;
}
#else
static double now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}
#endif

/* tiny portable random number generator so datasets are the same everywhere */
static unsigned int rngState = 12345u;
static int rnd_range(int lo, int hi) {
    rngState = rngState * 1664525u + 1013904223u;
    return lo + (int)((rngState >> 8) % (unsigned int)(hi - lo + 1));
}


/* ============================================================================
 *   COMPONENT 1 : DATA INGESTION AND VALIDATION MODULE
 *   MEMBER      : Sanskriti (590022775)
 *   JOB         : read the road data, find missing / duplicate / invalid
 *                 records, apply the treatment policy, keep a cleaning log.
 *                 Also makes the small / medium / large datasets.
 *
 *   CSV FORMAT (see sample_small.csv)
 *       NODE,<name>                           declares a junction
 *       ENTRY,<node>,<demand veh/min>         traffic enters here
 *       EXIT,<node>                           traffic leaves here
 *       edge_id,from,to,capacity,window,road_type,status      (one road)
 *   Lines starting with # and the header line are skipped.
 *
 *   TREATMENT POLICY (from the synopsis)
 *       missing capacity ........ record rejected and logged
 *       duplicate edge .......... capacities merged, warning logged
 *       negative / self loop /
 *       unknown node ............ record rejected with reason
 *       closed road ............. capacity set to 0
 * ========================================================================== */

static void ds_init(Dataset *d) { memset(d, 0, sizeof(*d)); }

static void ds_free(Dataset *d) {
    free(d->names); free(d->roads);
    free(d->entryNode); free(d->entryDemand); free(d->exitNode);
    memset(d, 0, sizeof(*d));
}

static void log_msg(Dataset *d, const char *fmt, ...) {
    if (d->nLog >= LOG_MAX) { d->logDropped++; return; }
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(d->log[d->nLog], LOG_LEN, fmt, ap);
    va_end(ap);
    d->nLog++;
}

static char *trim(char *s) {
    while (*s == ' ' || *s == '\t') s++;
    size_t len = strlen(s);
    while (len > 0 && (s[len-1] == ' ' || s[len-1] == '\t' ||
                       s[len-1] == '\r' || s[len-1] == '\n')) s[--len] = '\0';
    return s;
}

static int split_csv(char *line, char **f, int maxf) {
    int n = 0;
    char *p = line;
    while (n < maxf) {
        f[n++] = p;
        char *c = strchr(p, ',');
        if (!c || n == maxf) break;
        *c = '\0';
        p = c + 1;
    }
    for (int i = 0; i < n; i++) f[i] = trim(f[i]);
    return n;
}

static int parse_ll(const char *s, long long *out) {
    char *end;
    if (*s == '\0') return 0;
    errno = 0;
    long long v = strtoll(s, &end, 10);
    if (*end != '\0' || errno != 0) return 0;
    *out = v;
    return 1;
}

/* ---- basic building blocks (also used by the generators and tests) ---- */
static int ds_new_node(Dataset *d, const char *name) {
    GROW(d->names, d->nNodes, d->capNodes);
    strncpy(d->names[d->nNodes], name, NAME_LEN - 1);
    d->names[d->nNodes][NAME_LEN - 1] = '\0';
    return d->nNodes++;
}

static int find_node(const Dataset *d, const char *name) {
    for (int i = 0; i < d->nNodes; i++)
        if (strcmp(d->names[i], name) == 0) return i;
    return -1;
}

static int find_road(const Dataset *d, int from, int to) {
    for (int i = 0; i < d->nRoads; i++)
        if (d->roads[i].from == from && d->roads[i].to == to) return i;
    return -1;
}

static void ds_add_road(Dataset *d, const char *id, int from, int to, long long cap,
                        const char *window, const char *type, const char *status) {
    GROW(d->roads, d->nRoads, d->capRoads);
    Road *r = &d->roads[d->nRoads++];
    strncpy(r->id, id, FIELD_LEN - 1);         r->id[FIELD_LEN - 1] = '\0';
    strncpy(r->window, window, FIELD_LEN - 1); r->window[FIELD_LEN - 1] = '\0';
    strncpy(r->type, type, FIELD_LEN - 1);     r->type[FIELD_LEN - 1] = '\0';
    strncpy(r->status, status, FIELD_LEN - 1); r->status[FIELD_LEN - 1] = '\0';
    r->from = from; r->to = to; r->cap = cap;
}

static void ds_add_entry(Dataset *d, int node, long long demand) {
    GROW(d->entryNode, d->nEntry, d->capEntry);
    d->entryDemand = realloc(d->entryDemand, (size_t)d->capEntry * sizeof(long long));
    d->entryNode[d->nEntry] = node;
    d->entryDemand[d->nEntry] = demand;
    d->nEntry++;
}

static void ds_add_exit(Dataset *d, int node) {
    GROW(d->exitNode, d->nExit, d->capExit);
    d->exitNode[d->nExit++] = node;
}

static void reject(Dataset *d, int lineNo, const char *why) {
    d->rejected++;
    log_msg(d, "line %d: REJECTED - %s", lineNo, why);
}

/* ---- the CSV loader with all the validation ---- */
static int load_csv(Dataset *d, const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) return -1;
    strncpy(d->source, path, sizeof(d->source) - 1);

    char line[256];
    int lineNo = 0;
    while (fgets(line, sizeof(line), fp)) {
        lineNo++;
        char *s = trim(line);
        if (s[0] == '\0' || s[0] == '#') continue;

        char *f[8];
        int nf = split_csv(s, f, 8);
        if (strcmp(f[0], "edge_id") == 0) continue;          /* header */

        d->linesRead++;

        /* ---------- NODE ---------- */
        if (strcmp(f[0], "NODE") == 0) {
            if (nf < 2 || f[1][0] == '\0') { reject(d, lineNo, "NODE has no name"); continue; }
            if (strlen(f[1]) >= NAME_LEN)  { reject(d, lineNo, "node name too long"); continue; }
            if (find_node(d, f[1]) >= 0) {
                d->accepted++;
                log_msg(d, "line %d: warning - node %s declared twice, ignored", lineNo, f[1]);
                continue;
            }
            ds_new_node(d, f[1]);
            d->accepted++;
            continue;
        }

        /* ---------- ENTRY ---------- */
        if (strcmp(f[0], "ENTRY") == 0) {
            long long dem;
            if (nf < 3 || f[2][0] == '\0') { reject(d, lineNo, "ENTRY has no demand"); continue; }
            int node = find_node(d, f[1]);
            if (node < 0)                  { reject(d, lineNo, "ENTRY uses unknown node"); continue; }
            if (!parse_ll(f[2], &dem))     { reject(d, lineNo, "ENTRY demand is not a number"); continue; }
            if (dem < 0 || dem > MAX_CAP)  { reject(d, lineNo, "ENTRY demand out of range"); continue; }
            ds_add_entry(d, node, dem);
            d->accepted++;
            continue;
        }

        /* ---------- EXIT ---------- */
        if (strcmp(f[0], "EXIT") == 0) {
            int node = (nf >= 2) ? find_node(d, f[1]) : -1;
            if (node < 0) { reject(d, lineNo, "EXIT uses unknown node"); continue; }
            ds_add_exit(d, node);
            d->accepted++;
            continue;
        }

        /* ---------- ROAD RECORD ---------- */
        if (nf < 4) { reject(d, lineNo, "too few fields in road record"); continue; }
        const char *id     = f[0];
        const char *window = (nf > 4 && f[4][0]) ? f[4] : "peak";
        const char *type   = (nf > 5 && f[5][0]) ? f[5] : "road";
        const char *status = (nf > 6 && f[6][0]) ? f[6] : "open";

        if (f[1][0] == '\0' || f[2][0] == '\0') { reject(d, lineNo, "missing from/to node"); continue; }
        int u = find_node(d, f[1]);
        int v = find_node(d, f[2]);
        if (u < 0 || v < 0)            { reject(d, lineNo, "unknown node"); continue; }
        if (u == v)                    { reject(d, lineNo, "self loop"); continue; }
        if (f[3][0] == '\0')           { reject(d, lineNo, "missing capacity"); continue; }

        long long cap;
        if (!parse_ll(f[3], &cap))     { reject(d, lineNo, "capacity is not a number"); continue; }
        if (cap < 0)                   { reject(d, lineNo, "negative capacity"); continue; }
        if (cap > MAX_CAP)             { reject(d, lineNo, "capacity too large (> 1e9)"); continue; }
        if (strcmp(status, "open") && strcmp(status, "closed") && strcmp(status, "incident")) {
            reject(d, lineNo, "status must be open / closed / incident"); continue;
        }

        if (strcmp(status, "closed") == 0) {         /* closed road -> capacity 0 */
            cap = 0;
            d->closedRoads++;
            log_msg(d, "line %d: note - road %s is closed, capacity set to 0", lineNo, id);
        } else if (strcmp(status, "incident") == 0) {
            log_msg(d, "line %d: note - road %s has an incident, check its capacity", lineNo, id);
        }

        int old = find_road(d, u, v);
        if (old >= 0) {                              /* duplicate edge -> merge */
            d->roads[old].cap += cap;
            d->merged++;
            d->accepted++;
            log_msg(d, "line %d: warning - duplicate %s->%s, capacity merged into %s",
                    lineNo, f[1], f[2], d->roads[old].id);
            continue;
        }
        ds_add_road(d, id, u, v, cap, window, type, status);
        d->accepted++;
    }
    fclose(fp);

    if (d->nNodes == 0) log_msg(d, "warning - file has no NODE lines");
    return 0;
}

/* ---- dataset generators ---- */

/* the hand verifiable example of the synopsis (answer = 17) */
static void generate_small(Dataset *d) {
    strcpy(d->source, "built-in small example");
    int a = ds_new_node(d, "A");
    int b = ds_new_node(d, "B");
    int t = ds_new_node(d, "T");
    ds_add_entry(d, a, 10);
    ds_add_entry(d, b, 8);
    ds_add_exit(d, t);
    ds_add_road(d, "R1", a, b, 2, "peak", "arterial", "open");
    ds_add_road(d, "R2", a, t, 8, "peak", "arterial", "open");
    ds_add_road(d, "R3", b, t, 9, "peak", "arterial", "open");
    log_msg(d, "built-in example, no cleaning needed");
    d->linesRead = d->accepted = 9;
}

/* synthetic grid of junctions: medium = 20x25, large = 100x110 with diagonals */
static void generate_grid(Dataset *d, int rows, int cols, int diag, long long capScale) {
    char name[NAME_LEN], id[FIELD_LEN];
    snprintf(d->source, sizeof(d->source), "synthetic grid %dx%d", rows, cols);
    rngState = 12345u;                                /* same data every time */

    for (int i = 0; i < rows * cols; i++) {
        snprintf(name, sizeof(name), "N%d", i);
        ds_new_node(d, name);
    }
    int k = 0;
    #define ADD_BOTH(U, V) do { \
        snprintf(id, sizeof(id), "G%d", ++k); \
        ds_add_road(d, id, (U), (V), (long long)rnd_range(5, 30) * capScale, "peak", "street", "open"); \
        snprintf(id, sizeof(id), "G%d", ++k); \
        ds_add_road(d, id, (V), (U), (long long)rnd_range(5, 30) * capScale, "peak", "street", "open"); \
    } while (0)

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int u = r * cols + c;
            if (c + 1 < cols) ADD_BOTH(u, u + 1);
            if (r + 1 < rows) ADD_BOTH(u, u + cols);
            if (diag && r + 1 < rows && c + 1 < cols) ADD_BOTH(u, u + cols + 1);
        }
    }
    #undef ADD_BOTH

    for (int r = 0; r < rows; r++) {                  /* left column = entries  */
        ds_add_entry(d, r * cols, 40 * capScale);
        ds_add_exit(d, r * cols + cols - 1);          /* right column = exits   */
    }
    log_msg(d, "synthetic data, generated with a fixed seed, no cleaning needed");
    d->linesRead = d->accepted = d->nNodes + d->nRoads + d->nEntry + d->nExit;
}

static void print_cleaning_report(const Dataset *d) {
    printf(" Source file      : %s\n", d->source[0] ? d->source : "(none)");
    printf(" Records read     : %d\n", d->linesRead);
    printf(" Records accepted : %d\n", d->accepted);
    printf(" Records rejected : %d\n", d->rejected);
    printf(" Duplicates merged: %d\n", d->merged);
    printf(" Closed roads     : %d\n", d->closedRoads);
    printf("\n Cleaning log:\n");
    if (d->nLog == 0) printf("   (nothing to report, data was clean)\n");
    for (int i = 0; i < d->nLog; i++) printf("   %s\n", d->log[i]);
    if (d->logDropped) printf("   ... %d more messages not shown\n", d->logDropped);
}


/* ============================================================================
 *   COMPONENT 2 : GRAPH MODEL BUILDER
 *   MEMBER      : Radhika Mehrotra (590025253)
 *   JOB         : turn the clean dataset into a flow network G = (V, E).
 *                 junction -> node, road -> directed edge with capacity.
 *                 Adds a super source S (joined to every entry point) and a
 *                 super sink T (receiving from every exit point).
 *
 *   Every edge is stored together with its reverse edge:
 *        edge e   = forward edge  (capacity c)
 *        edge e^1 = reverse edge  (capacity 0, will hold the flow)
 *   so cap[e] is always the residual capacity c_f(u,v) = c(u,v) - f(u,v).
 *   Adjacency lists are sorted by node number, so when two paths have the
 *   same length the one through the LOWEST node ID is chosen (tie rule).
 * ========================================================================== */

static const Graph *sortG;                       /* used by qsort comparator */

static int cmp_adj(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    if (sortG->to[x] != sortG->to[y]) return sortG->to[x] - sortG->to[y];
    return x - y;
}

static void add_edge(Graph *g, int *k, int u, int v, long long c, int road) {
    int e = *k;
    g->from[e] = u;   g->to[e] = v;   g->cap[e] = c; g->orig[e] = c;   g->roadIdx[e] = road;
    g->from[e+1] = v; g->to[e+1] = u; g->cap[e+1] = 0; g->orig[e+1] = 0; g->roadIdx[e+1] = road;
    *k += 2;
}

static void build_graph(const Dataset *d, Graph *g) {
    int nEdges = d->nRoads + d->nEntry + d->nExit;
    memset(g, 0, sizeof(*g));
    g->ds = d;
    g->nReal = d->nNodes;
    g->n = d->nNodes + 2;
    g->S = d->nNodes;
    g->T = d->nNodes + 1;
    g->m = 2 * nEdges;

    g->from    = xmalloc(g->m * sizeof(int));
    g->to      = xmalloc(g->m * sizeof(int));
    g->roadIdx = xmalloc(g->m * sizeof(int));
    g->cap     = xmalloc(g->m * sizeof(long long));
    g->orig    = xmalloc(g->m * sizeof(long long));

    int k = 0;
    for (int i = 0; i < d->nRoads; i++)                     /* road segments   */
        add_edge(g, &k, d->roads[i].from, d->roads[i].to, d->roads[i].cap, i);
    for (int i = 0; i < d->nEntry; i++)                     /* S -> entry      */
        add_edge(g, &k, g->S, d->entryNode[i], d->entryDemand[i], -1);
    for (int i = 0; i < d->nExit; i++)                      /* exit -> T       */
        add_edge(g, &k, d->exitNode[i], g->T, INF_CAP, -1);

    /* adjacency lists in compressed form */
    g->adjStart = xcalloc(g->n + 1, sizeof(int));
    g->adj = xmalloc(g->m * sizeof(int));
    for (int e = 0; e < g->m; e++) g->adjStart[g->from[e] + 1]++;
    for (int u = 0; u < g->n; u++) g->adjStart[u + 1] += g->adjStart[u];
    int *pos = xmalloc(g->n * sizeof(int));
    memcpy(pos, g->adjStart, g->n * sizeof(int));
    for (int e = 0; e < g->m; e++) g->adj[pos[g->from[e]]++] = e;
    free(pos);

    sortG = g;
    for (int u = 0; u < g->n; u++)
        qsort(g->adj + g->adjStart[u], g->adjStart[u + 1] - g->adjStart[u], sizeof(int), cmp_adj);
}

static void free_graph(Graph *g) {
    free(g->from); free(g->to); free(g->roadIdx);
    free(g->cap);  free(g->orig);
    free(g->adjStart); free(g->adj);
    memset(g, 0, sizeof(*g));
}

/* put every edge back to "no flow" so another algorithm can run */
static void reset_flow(Graph *g) {
    for (int e = 0; e < g->m; e++) g->cap[e] = g->orig[e];
}

/* approximate memory used by the graph arrays, in bytes */
static size_t graph_bytes(const Graph *g) {
    return (size_t)g->m * (3 * sizeof(int) + 2 * sizeof(long long) + sizeof(int))
         + (size_t)(g->n + 1) * sizeof(int);
}

static void node_label(const Graph *g, int id, char *buf, size_t size) {
    if (id == g->S)      snprintf(buf, size, "SOURCE");
    else if (id == g->T) snprintf(buf, size, "SINK");
    else                 snprintf(buf, size, "%s", g->ds->names[id]);
}


/* ============================================================================
 *   COMPONENT 3 : MAXIMUM FLOW ENGINE
 *   MEMBER      : Anshul Bartwal (590027937)
 *   JOB         : Edmonds-Karp (Ford-Fulkerson with BFS shortest paths).
 *                 Greedy rule : always augment along the SHORTEST path.
 *                 Stopping    : no S -> T path left in the residual graph.
 *                 Gives trace output + counters, the minimum cut, and a
 *                 checker for the flow invariants.
 *
 *   Complexity: O(V*E) augmentations, each BFS costs O(E)  =>  O(V * E^2)
 * ========================================================================== */

/*
 * BFS on the residual graph. parent[v] = edge used to reach v.
 * forwardOnly = 1 is used by the greedy baseline (Component 4): it never
 * uses reverse edges, so it can never undo a bad decision.
 */
static int bfs_find_path(Graph *g, int *parent, int *queue, Counters *c, int forwardOnly) {
    for (int i = 0; i < g->n; i++) parent[i] = -1;
    parent[g->S] = -2;
    int head = 0, tail = 0;
    queue[tail++] = g->S;
    c->searches++;

    while (head < tail) {
        int u = queue[head++];
        for (int k = g->adjStart[u]; k < g->adjStart[u + 1]; k++) {
            int e = g->adj[k];
            int v = g->to[e];
            c->relaxations++;
            if (g->cap[e] > 0 && parent[v] == -1 && (!forwardOnly || g->orig[e] > 0)) {
                parent[v] = e;
                if (v == g->T) return 1;
                queue[tail++] = v;
            }
        }
    }
    return 0;
}

/* b = min residual capacity along the path found (the bottleneck) */
static long long path_bottleneck(const Graph *g, const int *parent) {
    long long b = LLONG_MAX;
    for (int v = g->T; v != g->S; v = g->from[parent[v]])
        if (g->cap[parent[v]] < b) b = g->cap[parent[v]];
    return b;
}

/* f(u,v) += b ; f(v,u) -= b   (done on the residual capacities) */
static void apply_path(Graph *g, const int *parent, long long b) {
    for (int v = g->T; v != g->S; v = g->from[parent[v]]) {
        int e = parent[v];
        g->cap[e]     -= b;
        g->cap[e ^ 1] += b;
    }
}

static void trace_step(const Graph *g, const int *parent, long long step, long long b, long long total) {
    int *nodes = xmalloc(g->n * sizeof(int));
    int len = 0;
    for (int v = g->T; v != g->S; v = g->from[parent[v]]) nodes[len++] = v;
    nodes[len++] = g->S;

    char lab[NAME_LEN + 8];
    printf("  %3lld. ", step);
    for (int i = len - 1; i >= 0; i--) {
        if (len > 12 && i == len - 7) { printf("... -> "); i = 3; }
        node_label(g, nodes[i], lab, sizeof(lab));
        printf("%s%s", lab, i > 0 ? " -> " : "");
    }
    printf("   bottleneck=%lld  total=%lld\n", b, total);
    free(nodes);
}

long long edmonds_karp(Graph *g, Counters *c) {
    int *parent = xmalloc(g->n * sizeof(int));
    int *queue  = xmalloc(g->n * sizeof(int));
    long long flow = 0;

    while (bfs_find_path(g, parent, queue, c, 0)) {
        long long b = path_bottleneck(g, parent);
        c->augmentations++;
        flow += b;
        if (g_trace) {
            if (c->augmentations <= TRACE_LIMIT) trace_step(g, parent, c->augmentations, b, flow);
            else if (c->augmentations == TRACE_LIMIT + 1) printf("  ... (trace stops after %d steps)\n", TRACE_LIMIT);
        }
        apply_path(g, parent, b);
    }
    free(parent); free(queue);
    return flow;
}

/* total flow = what leaves the super source */
static long long total_flow(const Graph *g) {
    long long f = 0;
    for (int e = 0; e < g->m; e += 2)
        if (g->from[e] == g->S) f += g->orig[e] - g->cap[e];
    return f;
}

/* R = nodes reachable from S in the final residual graph (the min cut side) */
static void reachable_from_source(const Graph *g, char *reach) {
    int *queue = xmalloc(g->n * sizeof(int));
    memset(reach, 0, g->n);
    int head = 0, tail = 0;
    queue[tail++] = g->S;
    reach[g->S] = 1;
    while (head < tail) {
        int u = queue[head++];
        for (int k = g->adjStart[u]; k < g->adjStart[u + 1]; k++) {
            int e = g->adj[k];
            if (g->cap[e] > 0 && !reach[g->to[e]]) {
                reach[g->to[e]] = 1;
                queue[tail++] = g->to[e];
            }
        }
    }
    free(queue);
}

/* capacity of the cut (R, V\R) */
static long long min_cut_value(const Graph *g, const char *reach) {
    long long cut = 0;
    for (int e = 0; e < g->m; e++)
        if (g->orig[e] > 0 && reach[g->from[e]] && !reach[g->to[e]]) cut += g->orig[e];
    return cut;
}

/*
 * Loop invariant checker. Returns the number of violations (should be 0):
 *   1. 0 <= f(u,v) <= c(u,v) on every edge
 *   2. reverse edge holds exactly the flow
 *   3. inflow = outflow at every junction except S and T
 */
static int check_constraints(const Graph *g) {
    int bad = 0;
    long long *net = xcalloc(g->n, sizeof(long long));
    for (int e = 0; e < g->m; e += 2) {
        long long f = g->orig[e] - g->cap[e];
        if (f < 0 || f > g->orig[e]) bad++;
        if (g->cap[e + 1] != f) bad++;
        net[g->from[e]] -= f;
        net[g->to[e]]   += f;
    }
    for (int v = 0; v < g->n; v++)
        if (v != g->S && v != g->T && net[v] != 0) bad++;
    free(net);
    return bad;
}


/* ============================================================================
 *   COMPONENT 4 : BASELINE AND BENCHMARKING MODULE
 *   MEMBER      : Vedansh Singh (590022205)
 *   JOB         : the algorithms we compare Edmonds-Karp against:
 *                   - DFS Ford-Fulkerson    O(E * |f*|)
 *                   - Greedy shortest path  (no reverse edges, heuristic)
 *                   - Brute force min cut   O(2^V * E), small graphs only
 *                 plus repeated timed runs, memory estimate, a text plot
 *                 and the check of measured work against O(V*E^2).
 * ========================================================================== */

/* DFS version: any path will do, found with an explicit stack */
long long dfs_ford_fulkerson(Graph *g, Counters *c) {
    int *parent = xmalloc(g->n * sizeof(int));
    int *it     = xmalloc(g->n * sizeof(int));
    int *stack  = xmalloc(g->n * sizeof(int));
    long long flow = 0;

    for (;;) {
        for (int i = 0; i < g->n; i++) { parent[i] = -1; it[i] = g->adjStart[i]; }
        parent[g->S] = -2;
        int sp = 0, found = 0;
        stack[sp++] = g->S;
        c->searches++;

        while (sp > 0) {
            int u = stack[sp - 1];
            if (u == g->T) { found = 1; break; }
            if (it[u] < g->adjStart[u + 1]) {
                int e = g->adj[it[u]++];
                int v = g->to[e];
                c->relaxations++;
                if (g->cap[e] > 0 && parent[v] == -1) {
                    parent[v] = e;
                    stack[sp++] = v;
                }
            } else sp--;
        }
        if (!found) break;

        long long b = path_bottleneck(g, parent);
        apply_path(g, parent, b);
        flow += b;
        c->augmentations++;
    }
    free(parent); free(it); free(stack);
    return flow;
}

/* Greedy heuristic: shortest path again and again, but never cancels flow */
long long greedy_shortest_path(Graph *g, Counters *c) {
    int *parent = xmalloc(g->n * sizeof(int));
    int *queue  = xmalloc(g->n * sizeof(int));
    long long flow = 0;
    while (bfs_find_path(g, parent, queue, c, 1)) {
        long long b = path_bottleneck(g, parent);
        apply_path(g, parent, b);
        flow += b;
        c->augmentations++;
    }
    free(parent); free(queue);
    return flow;
}

/*
 * Brute force: try every set X of junctions on the source side, cut
 * capacity = sum of c(u,v) for u in {S}+X and v outside. The smallest one
 * is the min cut. 2^V cuts, so only used to validate small cases.
 * Returns -1 if the graph is too big.
 */
static long long brute_force_min_cut(const Graph *g, long long *subsets) {
    int k = g->nReal;
    if (k > BRUTE_MAX_NODES) return -1;
    char *inR = xcalloc(g->n, 1);
    long long best = LLONG_MAX;
    *subsets = 0;

    for (unsigned long mask = 0; mask < (1UL << k); mask++) {
        for (int i = 0; i < k; i++) inR[i] = (char)((mask >> i) & 1);
        inR[g->S] = 1;
        inR[g->T] = 0;
        long long cut = 0;
        for (int e = 0; e < g->m; e++)
            if (g->orig[e] > 0 && inR[g->from[e]] && !inR[g->to[e]]) cut += g->orig[e];
        if (cut < best) best = cut;
        (*subsets)++;
    }
    free(inR);
    return best;
}

/* ---- timed runs ---- */
typedef long long (*FlowFn)(Graph *, Counters *);

typedef struct {
    const char *name;
    FlowFn fn;
    long long flow;
    double mean, min, max;
    Counters c;
    size_t memBytes;
} BenchRes;

static void bench_one(Graph *g, BenchRes *r, int runs) {
    double sum = 0;
    r->min = 1e30; r->max = 0;
    for (int i = 0; i < runs; i++) {
        Counters c = {0, 0, 0};
        reset_flow(g);
        double t0 = now_ms();
        long long f = r->fn(g, &c);
        double t = now_ms() - t0;
        sum += t;
        if (t < r->min) r->min = t;
        if (t > r->max) r->max = t;
        r->flow = f;
        r->c = c;
    }
    r->mean = sum / runs;
}

/* O(V*E^2) worst case versus what we really measured */
static void complexity_check(const Graph *g, const Counters *ek) {
    double V = g->n, E = g->m / 2;
    double worst = V * E * E;
    printf("\n Asymptotic analysis (Edmonds-Karp)\n");
    printf("   V = %.0f , E = %.0f\n", V, E);
    printf("   worst case  V*E^2              = %.3e\n", worst);
    printf("   measured edge relaxations      = %lld\n", ek->relaxations);
    printf("   measured / worst case          = %.2e\n", (double)ek->relaxations / worst);
    printf("   augmentations (bound V*E = %.0f) = %lld\n", V * E, ek->augmentations);
    printf("   -> real road-like graphs run far below the worst case because\n");
    printf("      BFS stops early and few edges become the bottleneck.\n");
}

static void run_benchmark(Graph *g, int runs) {
    BenchRes res[3] = {
        { "Edmonds-Karp",   edmonds_karp,         0, 0, 0, 0, {0,0,0}, 0 },
        { "DFS Ford-Fulk.", dfs_ford_fulkerson,   0, 0, 0, 0, {0,0,0}, 0 },
        { "Greedy shortest", greedy_shortest_path, 0, 0, 0, 0, {0,0,0}, 0 }
    };
    int saveTrace = g_trace;
    g_trace = 0;

    for (int i = 0; i < 3; i++) bench_one(g, &res[i], runs);
    g_trace = saveTrace;

    size_t base = graph_bytes(g);
    res[0].memBytes = base + 2 * (size_t)g->n * sizeof(int);       /* parent, queue        */
    res[1].memBytes = base + 3 * (size_t)g->n * sizeof(int);       /* parent, it, stack    */
    res[2].memBytes = base + 2 * (size_t)g->n * sizeof(int);

    printf("\n Each algorithm run %d times on the same network.\n\n", runs);
    printf(" %-16s %9s %6s %9s %9s %9s %11s %7s\n",
           "Algorithm", "Flow", "Gap%", "Mean ms", "Searches", "Augment.", "Relaxations", "Mem KB");
    printf(" %.*s\n", LINE_W + 8, "------------------------------------------------------------------------------------");
    for (int i = 0; i < 3; i++) {
        double gap = res[0].flow > 0 ? 100.0 * (double)(res[0].flow - res[i].flow) / (double)res[0].flow : 0.0;
        printf(" %-16s %9lld %6.2f %9.3f %9lld %9lld %11lld %7.1f\n",
               res[i].name, res[i].flow, gap, res[i].mean,
               res[i].c.searches, res[i].c.augmentations, res[i].c.relaxations,
               res[i].memBytes / 1024.0);
    }
    printf("\n Gap%% = distance from the best known answer (Edmonds-Karp is optimal).\n");
    printf(" Memory is an estimate of the arrays allocated, not measured from the OS.\n");

    /* text plot of the mean runtime */
    double top = res[0].mean;
    for (int i = 1; i < 3; i++) if (res[i].mean > top) top = res[i].mean;
    if (top <= 0) top = 1e-9;
    printf("\n Mean runtime plot (each # is about %.4f ms)\n", top / 40.0);
    for (int i = 0; i < 3; i++) {
        int bars = (int)(40.0 * res[i].mean / top + 0.5);
        if (bars < 1) bars = 1;
        printf(" %-16s |", res[i].name);
        for (int j = 0; j < bars; j++) putchar('#');
        printf(" %.3f ms  (min %.3f, max %.3f)\n", res[i].mean, res[i].min, res[i].max);
    }
    complexity_check(g, &res[0].c);
}


/* ============================================================================
 *   COMPONENT 5 : EXPLANATION AND REPORTING LAYER   (+ the text interface)
 *   MEMBER      : Dhruv Pratap Chauhan (590023965)
 *   JOB         : everything the traffic officer sees: menu screens, the
 *                 report with throughput, unmet demand, bottleneck roads and
 *                 advice like "Extend green time on Road X".
 *                 Theme: white, black and grey only.
 * ========================================================================== */

#define CLR_RESET "\033[0m"
#define CLR_HEAD  "\033[30;47m"      /* black text on white bar */
#define CLR_GREY  "\033[90m"         /* grey text               */
#define CLR_BOLD  "\033[1m"

static void ui_clear(void) {
    if (useColor) printf("\033[2J\033[H");
    else printf("\n\n");
}

static void ui_rule(void) {
    if (useColor) printf(CLR_GREY);
    for (int i = 0; i < LINE_W; i++) putchar('-');
    if (useColor) printf(CLR_RESET);
    putchar('\n');
}

static void ui_head(const char *title) {
    if (useColor) printf(CLR_HEAD);
    printf(" %-*s ", LINE_W - 2, title);
    if (useColor) printf(CLR_RESET);
    putchar('\n');
}

static void ui_grey(const char *text) {
    if (useColor) printf(CLR_GREY "%s" CLR_RESET, text);
    else printf("%s", text);
}

static void read_line(const char *prompt, char *buf, int size) {
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, size, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static void pause_screen(void) {
    char tmp[16];
    read_line("\n Press Enter to continue...", tmp, sizeof(tmp));
}

static void enable_ansi(void) {
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    DWORD mode = 0;
    if (h != INVALID_HANDLE_VALUE && GetConsoleMode(h, &mode))
        SetConsoleMode(h, mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
#endif
}

/* ---- program state shared by the screens ---- */
static Dataset DS;                 /* current dataset            */
static Graph   G;                  /* current flow network       */
static int dsLoaded = 0, graphBuilt = 0, flowDone = 0;
static long long lastFlow = 0;
static Counters  lastCnt;
static double    lastMs = 0;

static void drop_results(void) {
    if (graphBuilt) free_graph(&G);
    graphBuilt = flowDone = 0;
    lastFlow = 0;
    memset(&lastCnt, 0, sizeof(lastCnt));
}

static void new_dataset(void) {
    drop_results();
    if (dsLoaded) ds_free(&DS);
    ds_init(&DS);
    dsLoaded = 0;
}

static long long total_demand(const Dataset *d) {
    long long s = 0;
    for (int i = 0; i < d->nEntry; i++) s += d->entryDemand[i];
    return s;
}

/* build the graph if needed, run Edmonds-Karp and remember the result */
static void solve_current(int trace) {
    if (graphBuilt) free_graph(&G);
    build_graph(&DS, &G);
    graphBuilt = 1;
    memset(&lastCnt, 0, sizeof(lastCnt));
    g_trace = trace;
    double t0 = now_ms();
    lastFlow = edmonds_karp(&G, &lastCnt);
    lastMs = now_ms() - t0;
    g_trace = 0;
    flowDone = 1;
}

static void report_officer(void) {
    Graph *g = &G;
    Dataset *d = &DS;
    long long demand = total_demand(d);
    long long unmet = demand - lastFlow;
    char *reach = xcalloc(g->n, 1);
    reachable_from_source(g, reach);
    long long cut = min_cut_value(g, reach);
    int violations = check_constraints(g);

    ui_head("OFFICER REPORT");
    printf("\n");
    printf(" Network throughput (max flow)  : %lld vehicles/min\n", lastFlow);
    printf(" Total demand at entry points   : %lld vehicles/min\n", demand);
    printf(" Unmet demand                   : %lld vehicles/min (%.1f%%)\n",
           unmet, demand > 0 ? 100.0 * (double)unmet / (double)demand : 0.0);
    printf(" Minimum cut capacity           : %lld   %s\n", cut,
           cut == lastFlow ? "(equals the flow, so the flow is maximum)" : "(MISMATCH!)");
    printf(" Constraint violations          : %d\n", violations);
    printf(" Closed roads (carry no traffic): %d\n", d->closedRoads);

    /* ---- demand served at each entry point ---- */
    printf("\n Entry points\n");
    ui_rule();
    printf(" %-16s %10s %10s %10s\n", "Junction", "Demand", "Served", "Unmet");
    int shown = 0;
    for (int i = 0; i < d->nEntry; i++) {
        int e = 2 * (d->nRoads + i);
        long long served = g->orig[e] - g->cap[e];
        if (shown < 12) {
            printf(" %-16s %10lld %10lld %10lld\n", d->names[d->entryNode[i]],
                   d->entryDemand[i], served, d->entryDemand[i] - served);
            shown++;
        }
    }
    if (d->nEntry > shown) { ui_grey(" ...\n"); printf(" (%d more entry points not shown)\n", d->nEntry - shown); }

    /* ---- bottleneck roads = edges of the minimum cut ---- */
    printf("\n Bottleneck roads (minimum cut)\n");
    ui_rule();
    int count = 0;
    for (int e = 0; e < g->m; e += 2) {
        if (g->roadIdx[e] < 0 || g->orig[e] <= 0) continue;
        if (reach[g->from[e]] && !reach[g->to[e]]) {
            if (count < 15) {
                Road *r = &d->roads[g->roadIdx[e]];
                printf(" %-8s %-12s -> %-12s  full at %lld veh/min\n", r->id,
                       d->names[r->from], d->names[r->to], g->orig[e]);
            }
            count++;
        }
    }
    if (count == 0) printf(" None. No road is holding traffic back.\n");
    if (count > 15) printf(" ... and %d more bottleneck roads\n", count - 15);

    /* ---- plain language advice ---- */
    printf("\n Advice\n");
    ui_rule();
    if (unmet == 0) {
        printf(" All demand can be served. No signal change is needed.\n");
    } else if (count == 0) {
        printf(" Demand is limited by the entry points, not by the roads.\n");
    } else {
        int printed = 0;
        for (int e = 0; e < g->m && printed < 10; e += 2) {
            if (g->roadIdx[e] < 0 || g->orig[e] <= 0) continue;
            if (reach[g->from[e]] && !reach[g->to[e]]) {
                Road *r = &d->roads[g->roadIdx[e]];
                printf(" - Extend green time on Road %s (%s -> %s). It is full at %lld veh/min.\n",
                       r->id, d->names[r->from], d->names[r->to], g->orig[e]);
                printed++;
            }
        }
        if (count > printed) printf(" - (%d more roads in the bottleneck list above)\n", count - printed);
        printf(" - Widening any road that is NOT in the list will not raise throughput.\n");
    }
    if (g->n > 5000)
        printf(" - Network is large: Dinic's algorithm O(V^2 E) would be faster than Edmonds-Karp.\n");
    printf(" - If journey time matters, use min cost max flow (this model ignores delay).\n");
    free(reach);
}

static void screen_status(void) {
    if (dsLoaded)
        printf(" Dataset : %s  (%d junctions, %d roads, %d entries, %d exits)\n",
               DS.source, DS.nNodes, DS.nRoads, DS.nEntry, DS.nExit);
    else
        printf(" Dataset : none loaded\n");
    if (graphBuilt)
        printf(" Graph   : built  (%d nodes incl. source/sink, %d edges)\n", G.n, G.m / 2);
    else
        printf(" Graph   : not built\n");
    if (flowDone)
        printf(" Result  : max flow = %lld veh/min  (%.3f ms)\n", lastFlow, lastMs);
    else
        printf(" Result  : not computed\n");
}

static void screen_menu(void) {
    ui_clear();
    ui_head("URBAN TRAFFIC SIGNAL COORDINATOR");
    ui_grey(" DAA Project  |  Network Throughput Optimisation using Maximum Flow\n");
    ui_rule();
    screen_status();
    ui_rule();
    printf("  [1]  Load road data from a CSV file\n");
    printf("  [2]  Generate a dataset (small / medium / large)\n");
    printf("  [3]  Show data cleaning report\n");
    printf("  [4]  Build graph and run maximum flow\n");
    printf("  [5]  Officer report (throughput, bottlenecks, advice)\n");
    printf("  [6]  Benchmark: Edmonds-Karp vs DFS vs Greedy\n");
    printf("  [7]  Verify min cut with brute force (small data only)\n");
    printf("  [8]  Extreme capacity test\n");
    printf("  [9]  Run test suite\n");
    printf("  [C]  Colours on/off        [0]  Exit\n");
    ui_rule();
}

/* ---------- screens, one per menu option ---------- */

static void screen_load(void) {
    char path[120];
    ui_head("LOAD CSV FILE");
    ui_grey(" Try: sample_small.csv, sample_city.csv, sample_invalid.csv\n\n");
    read_line(" File name: ", path, sizeof(path));
    if (path[0] == '\0') { printf(" No file name given.\n"); return; }
    new_dataset();
    if (load_csv(&DS, path) != 0) {
        printf(" Could not open '%s'.\n", path);
        ds_free(&DS); ds_init(&DS);
        return;
    }
    dsLoaded = 1;
    printf("\n Loaded %d junctions, %d roads. %d records rejected, %d merged.\n",
           DS.nNodes, DS.nRoads, DS.rejected, DS.merged);
    if (DS.rejected || DS.merged) printf(" Choose option 3 to read the cleaning log.\n");
}

static void screen_generate(void) {
    char buf[16];
    ui_head("GENERATE DATASET");
    printf("\n  [1] Small   - 3 junctions, hand verifiable example (answer 17)\n");
    printf("  [2] Medium  - 20 x 25 grid, about 500 junctions, 1,900 roads\n");
    printf("  [3] Large   - 100 x 110 grid, 11,000 junctions, 65,000 roads\n\n");
    read_line(" Choice: ", buf, sizeof(buf));
    int c = atoi(buf);
    if (c < 1 || c > 3) { printf(" Cancelled.\n"); return; }
    new_dataset();
    if (c == 1) generate_small(&DS);
    if (c == 2) generate_grid(&DS, 20, 25, 0, 1);
    if (c == 3) generate_grid(&DS, 100, 110, 1, 1);
    dsLoaded = 1;
    printf("\n Generated: %d junctions, %d roads, %d entries, %d exits.\n",
           DS.nNodes, DS.nRoads, DS.nEntry, DS.nExit);
}

static void screen_run(void) {
    char buf[16];
    ui_head("MAXIMUM FLOW  (Edmonds-Karp)");
    if (!dsLoaded) { printf("\n Load or generate a dataset first (option 1 or 2).\n"); return; }
    int trace = 0;
    if (DS.nNodes <= 30) {
        read_line("\n Show every augmenting path? (y/n): ", buf, sizeof(buf));
        trace = (buf[0] == 'y' || buf[0] == 'Y');
    } else {
        printf("\n Large network, trace is off. Running...\n");
    }
    printf("\n");
    solve_current(trace);
    printf("\n Max flow        : %lld vehicles/min\n", lastFlow);
    printf(" Time            : %.3f ms\n", lastMs);
    printf(" BFS searches    : %lld\n", lastCnt.searches);
    printf(" Augmentations   : %lld\n", lastCnt.augmentations);
    printf(" Edge relaxations: %lld\n", lastCnt.relaxations);
    printf(" Violations      : %d\n", check_constraints(&G));
    printf("\n Use option 5 for the officer report.\n");
}

static void screen_benchmark(void) {
    char buf[16];
    ui_head("BENCHMARK");
    if (!dsLoaded) { printf("\n Load or generate a dataset first.\n"); return; }
    if (!graphBuilt) solve_current(0);
    int runs = 10;
    if (G.n > 5000) {
        read_line("\n Large network, each run takes a while. Number of runs (default 3): ", buf, sizeof(buf));
        runs = atoi(buf); if (runs < 1) runs = 3;
    } else {
        read_line("\n Number of runs (default 10): ", buf, sizeof(buf));
        runs = atoi(buf); if (runs < 1) runs = 10;
    }
    printf("\n Running...\n");
    run_benchmark(&G, runs);
    solve_current(0);                    /* put the Edmonds-Karp result back */
}

static void screen_brute(void) {
    ui_head("BRUTE FORCE MIN CUT CHECK");
    if (!dsLoaded) { printf("\n Load or generate a dataset first.\n"); return; }
    if (!flowDone) solve_current(0);
    if (DS.nNodes > BRUTE_MAX_NODES) {
        printf("\n Brute force needs 2^V cuts. %d junctions is too many (limit %d).\n",
               DS.nNodes, BRUTE_MAX_NODES);
        return;
    }
    long long subsets = 0;
    double t0 = now_ms();
    long long best = brute_force_min_cut(&G, &subsets);
    double ms = now_ms() - t0;
    printf("\n Cuts examined (2^%d)  : %lld\n", DS.nNodes, subsets);
    printf(" Smallest cut found    : %lld\n", best);
    printf(" Edmonds-Karp max flow : %lld\n", lastFlow);
    printf(" Brute force time      : %.3f ms\n", ms);
    printf("\n %s\n", best == lastFlow ? "MATCH: max flow = min cut, the answer is verified."
                                      : "MISMATCH: something is wrong!");
}

static void screen_extreme(void) {
    ui_head("EXTREME CAPACITY TEST");
    printf("\n Same 10 x 10 grid, every capacity multiplied by a large factor.\n");
    printf(" If an algorithm depends on the flow value, it will slow down.\n\n");
    printf(" %-10s %-14s | %-22s | %-22s\n", "Scale", "Max flow", "Edmonds-Karp", "DFS Ford-Fulkerson");
    printf(" %-10s %-14s | %-10s %-10s | %-10s %-10s\n", "", "", "augment.", "ms", "augment.", "ms");
    ui_rule();
    long long scales[3] = { 1, 1000, 1000000 };
    for (int i = 0; i < 3; i++) {
        Dataset *d = xmalloc(sizeof(Dataset));
        Graph g;
        Counters c1 = {0,0,0}, c2 = {0,0,0};
        ds_init(d);
        generate_grid(d, 10, 10, 0, scales[i]);
        build_graph(d, &g);
        double t0 = now_ms();
        long long f1 = edmonds_karp(&g, &c1);
        double t1 = now_ms() - t0;
        reset_flow(&g);
        t0 = now_ms();
        long long f2 = dfs_ford_fulkerson(&g, &c2);
        double t2 = now_ms() - t0;
        printf(" x%-9lld %-14lld | %-10lld %-10.3f | %-10lld %-10.3f %s\n",
               scales[i], f1, c1.augmentations, t1, c2.augmentations, t2,
               f1 == f2 ? "" : "(flows differ!)");
        free_graph(&g); ds_free(d); free(d);
    }
    printf("\n Observation: the flow value grew a million times but the work did not.\n");
    printf(" O(E*|f*|) for DFS Ford-Fulkerson is a WORST case bound. It is reached only\n");
    printf(" when the DFS keeps picking paths with tiny bottlenecks. Edmonds-Karp's\n");
    printf(" O(V*E^2) bound never depends on capacities, which is why it is the safe choice.\n");
}


/* ============================================================================
 *   COMPONENT 6 : TESTING AND EVALUATION SUITE
 *   MEMBER      : Dhruv Pratap Chauhan (590023965)
 *   JOB         : edge cases, invalid input test, stress test, and comparison
 *                 against independently verified answers.
 *                 Each test builds its own tiny dataset and checks the result.
 * ========================================================================== */

static int testsPassed = 0, testsFailed = 0;

static void check(const char *name, int ok) {
    printf("  [%s] %s\n", ok ? "PASS" : "FAIL", name);
    if (ok) testsPassed++; else testsFailed++;
}

/* build + solve a dataset, caller frees the graph */
static long long solve_dataset(Dataset *d, Graph *g, Counters *c) {
    memset(c, 0, sizeof(*c));
    build_graph(d, g);
    return edmonds_karp(g, c);
}

static void run_all_tests(void) {
    Dataset *d = xmalloc(sizeof(Dataset));
    Graph g;
    Counters c;
    long long f, subsets;
    testsPassed = testsFailed = 0;
    g_trace = 0;

    ui_head("TEST SUITE");
    printf("\n Verified answers and edge cases\n");
    ui_rule();

    /* 1 + 2 : hand verified example, confirmed by brute force */
    ds_init(d); generate_small(d);
    f = solve_dataset(d, &g, &c);
    check("hand example: max flow = 17 (worked out on paper)", f == 17);
    check("hand example: brute force min cut = 17 (independent check)",
          brute_force_min_cut(&g, &subsets) == 17);
    {
        char reach[8];
        reachable_from_source(&g, reach);
        check("hand example: min cut capacity equals the flow", min_cut_value(&g, reach) == f);
    }
    check("hand example: zero constraint violations", check_constraints(&g) == 0);
    free_graph(&g); ds_free(d);

    /* 3 : empty input */
    ds_init(d);
    f = solve_dataset(d, &g, &c);
    check("edge case 1: empty input -> flow 0, no crash", f == 0);
    free_graph(&g); ds_free(d);

    /* 4 : single node that is both entry and exit */
    ds_init(d);
    { int a = ds_new_node(d, "A"); ds_add_entry(d, a, 5); ds_add_exit(d, a); }
    f = solve_dataset(d, &g, &c);
    check("edge case 2: single node (entry = exit) -> flow = demand 5", f == 5);
    free_graph(&g); ds_free(d);

    /* 5 : disconnected source and sink */
    ds_init(d);
    {
        int a = ds_new_node(d, "A"), b = ds_new_node(d, "B"), t = ds_new_node(d, "T");
        ds_add_entry(d, a, 9); ds_add_exit(d, t);
        ds_add_road(d, "R1", a, b, 5, "peak", "main", "open");   /* no road reaches T */
    }
    f = solve_dataset(d, &g, &c);
    check("edge case 3: source and sink disconnected -> flow 0", f == 0);
    free_graph(&g); ds_free(d);

    /* 6 : zero capacity bottleneck */
    ds_init(d);
    {
        int a = ds_new_node(d, "A"), b = ds_new_node(d, "B"), t = ds_new_node(d, "T");
        ds_add_entry(d, a, 9); ds_add_exit(d, t);
        ds_add_road(d, "R1", a, b, 9, "peak", "main", "open");
        ds_add_road(d, "R2", b, t, 0, "peak", "main", "closed");
    }
    f = solve_dataset(d, &g, &c);
    check("edge case 4: zero capacity bottleneck -> flow 0", f == 0);
    free_graph(&g); ds_free(d);

    /* 7 : tied equal length paths, lowest node id must win */
    ds_init(d);
    {
        int p = ds_new_node(d, "P"), q1 = ds_new_node(d, "Q1"), q2 = ds_new_node(d, "Q2"), t = ds_new_node(d, "T");
        ds_add_entry(d, p, 4); ds_add_exit(d, t);
        ds_add_road(d, "R1", p, q1, 3, "peak", "main", "open");
        ds_add_road(d, "R2", p, q2, 3, "peak", "main", "open");
        ds_add_road(d, "R3", q1, t, 3, "peak", "main", "open");
        ds_add_road(d, "R4", q2, t, 3, "peak", "main", "open");
    }
    f = solve_dataset(d, &g, &c);
    {
        long long f1 = g.orig[0] - g.cap[0];       /* P->Q1 */
        long long f2 = g.orig[2] - g.cap[2];       /* P->Q2 */
        check("edge case 5: tied paths -> lowest node ID used first (3 and 1)",
              f == 4 && f1 == 3 && f2 == 1);
    }
    free_graph(&g); ds_free(d);

    /* 8 : invalid input file */
    printf("\n Invalid input test\n");
    ui_rule();
    {
        const char *tmp = "tmp_invalid_test.csv";
        FILE *fp = fopen(tmp, "w");
        if (fp) {
            fputs("NODE,A\nNODE,B\nNODE,T\nENTRY,A,10\nEXIT,T\n"
                  "R1,A,B,5,peak,main,open\n"
                  "R2,A,B,3,peak,main,open\n"        /* duplicate  -> merged   */
                  "R3,B,T,-4,peak,main,open\n"       /* negative   -> rejected */
                  "R4,B,Z,6,peak,main,open\n"        /* unknown    -> rejected */
                  "R5,B,B,6,peak,main,open\n"        /* self loop  -> rejected */
                  "R6,B,T,,peak,main,open\n"         /* missing    -> rejected */
                  "R7,B,T,9,peak,main,closed\n"      /* closed     -> cap 0    */
                  "R8,A,T,abc,peak,main,open\n", fp);/* not a number -> rejected */
            fclose(fp);
            ds_init(d);
            int rc = load_csv(d, tmp);
            check("loader opens the file", rc == 0);
            check("5 bad records rejected (negative, unknown node, self loop, missing, text)",
                  d->rejected == 5);
            check("duplicate edge merged (capacity 5 + 3 = 8)",
                  d->merged == 1 && d->nRoads == 2 && d->roads[0].cap == 8);
            check("closed road accepted with capacity 0",
                  d->closedRoads == 1 && d->roads[1].cap == 0);
            ds_free(d);
            remove(tmp);
        } else check("could not create temporary test file", 0);
    }

    /* 9 : extreme capacities */
    printf("\n Extreme values\n");
    ui_rule();
    {
        Counters ca, cb;
        long long fa, fb;
        ds_init(d);
        int a = ds_new_node(d, "A"), b = ds_new_node(d, "B"), t = ds_new_node(d, "T");
        long long C = 1000000000LL;
        ds_add_entry(d, a, C); ds_add_entry(d, b, C); ds_add_exit(d, t);
        ds_add_road(d, "R1", a, b, 1, "peak", "main", "open");
        ds_add_road(d, "R2", a, t, C, "peak", "main", "open");
        ds_add_road(d, "R3", b, t, C, "peak", "main", "open");
        fa = solve_dataset(d, &g, &ca);
        reset_flow(&g);
        memset(&cb, 0, sizeof(cb));
        fb = dfs_ford_fulkerson(&g, &cb);
        check("capacities of 1e9: Edmonds-Karp gives 2e9", fa == 2 * C);
        check("capacities of 1e9: DFS Ford-Fulkerson agrees", fb == fa);
        check("capacities of 1e9: Edmonds-Karp needs only a few augmentations", ca.augmentations <= 4);
        free_graph(&g); ds_free(d);
    }

    /* 10 : medium comparison */
    printf("\n Baseline comparison on medium data\n");
    ui_rule();
    {
        Counters c1, c2, c3;
        long long f1, f2, f3;
        ds_init(d); generate_grid(d, 20, 25, 0, 1);
        f1 = solve_dataset(d, &g, &c1);
        int viol = check_constraints(&g);
        reset_flow(&g); memset(&c2, 0, sizeof(c2)); f2 = dfs_ford_fulkerson(&g, &c2);
        reset_flow(&g); memset(&c3, 0, sizeof(c3)); f3 = greedy_shortest_path(&g, &c3);
        printf("     Edmonds-Karp = %lld, DFS = %lld, Greedy = %lld\n", f1, f2, f3);
        check("medium: zero constraint violations", viol == 0);
        check("medium: DFS Ford-Fulkerson reaches the same flow", f1 == f2);
        check("medium: greedy heuristic never beats the optimum", f3 <= f1);
        free_graph(&g); ds_free(d);
    }

    /* 11 : stress test */
    printf("\n Stress test (large data, may take a few seconds)\n");
    ui_rule();
    {
        ds_init(d); generate_grid(d, 100, 110, 1, 1);
        double t0 = now_ms();
        f = solve_dataset(d, &g, &c);
        double ms = now_ms() - t0;
        printf("     V = %d, E = %d, flow = %lld, time = %.1f ms, augmentations = %lld\n",
               g.n, g.m / 2, f, ms, c.augmentations);
        check("large: finished and flow is positive", f > 0);
        check("large: zero constraint violations", check_constraints(&g) == 0);
        free_graph(&g); ds_free(d);
    }

    free(d);
    printf("\n");
    ui_rule();
    printf(" Result: %d passed, %d failed\n", testsPassed, testsFailed);
}


/* ============================================================================
 *   MAIN : menu loop, connects all six components
 * ========================================================================== */

int main(void) {
    char buf[32];
    enable_ansi();
    ds_init(&DS);

    for (;;) {
        screen_menu();
        read_line(" Your choice: ", buf, sizeof(buf));
        printf("\n");

        switch (buf[0]) {
            case '1': screen_load();      break;
            case '2': screen_generate();  break;
            case '3':
                ui_head("DATA CLEANING REPORT");
                printf("\n");
                if (dsLoaded) print_cleaning_report(&DS);
                else printf(" No dataset yet.\n");
                break;
            case '4': screen_run();       break;
            case '5':
                if (!flowDone) { ui_head("OFFICER REPORT"); printf("\n Run option 4 first.\n"); }
                else report_officer();
                break;
            case '6': screen_benchmark(); break;
            case '7': screen_brute();     break;
            case '8': screen_extreme();   break;
            case '9': run_all_tests();    break;
            case 'c': case 'C':
                useColor = !useColor;
                printf(" Colours %s.\n", useColor ? "on" : "off");
                break;
            case '0':
                drop_results();
                if (dsLoaded) ds_free(&DS);
                printf(" Goodbye.\n");
                return 0;
            default:
                printf(" Please type a number from the menu.\n");
        }
        pause_screen();
    }
}