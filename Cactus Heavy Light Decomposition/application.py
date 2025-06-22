
import time
import random
from collections import defaultdict, deque

# Function to generate a random cactus graph
def generate_cactus(n, max_cycle_length=10, cycle_prob=0.3):
    adj = defaultdict(list)
    if n <= 1:
        if n == 1:
            adj[0] = []
        return adj
    base_size = max(2, int(n * 0.7))
    for v in range(1, base_size):
        u = random.randint(0, v - 1)
        w = random.randint(1, 10)
        adj[u].append((v, w))
        adj[v].append((u, w))
    current_n = base_size
    attach_points = list(range(base_size))
    while current_n < n and attach_points:
        if random.random() > cycle_prob:
            break
        v = random.choice(attach_points)
        rem = n - current_n
        if rem < 2:
            break
        max_len = min(max_cycle_length, rem + 1)
        if max_len < 3:
            break
        cycle_len = random.randint(3, max_len)
        new_nodes = list(range(current_n, current_n + cycle_len - 1))
        prev = v
        for u in new_nodes:
            w = random.randint(1, 10)
            adj[prev].append((u, w))
            adj[u].append((prev, w))
            prev = u
        w = random.randint(1, 10)
        adj[prev].append((v, w))
        adj[v].append((prev, w))
        for u in new_nodes:
            attach_points.append(u)
        current_n += (cycle_len - 1)
        if random.random() < 0.5:
            try:
                attach_points.remove(v)
            except ValueError:
                pass
    return adj

# Tarjan's algorithm for edge-biconnected components (edge-BCC)
def edge_bcc(adj):
    n = max(adj.keys()) + 1 if adj else 0
    disc = [-1] * n
    low = [0] * n
    parent = [-1] * n
    time_dfs = 0
    stack = []
    bcc_list = []

    def dfs(u):
        nonlocal time_dfs
        disc[u] = low[u] = time_dfs
        time_dfs += 1
        for v, _ in adj[u]:
            if disc[v] == -1:
                parent[v] = u
                stack.append((u, v))
                dfs(v)
                low[u] = min(low[u], low[v])
                if low[v] >= disc[u]:
                    comp = []
                    while stack:
                        e = stack.pop()
                        comp.append(e)
                        if e == (u, v):
                            break
                    bcc_list.append(comp)
            elif v != parent[u] and disc[v] < disc[u]:
                low[u] = min(low[u], disc[v])
                stack.append((u, v))

    for u in adj:
        if disc[u] == -1:
            dfs(u)
            if stack:
                comp = []
                while stack:
                    comp.append(stack.pop())
                bcc_list.append(comp)
    return bcc_list

# Block-tree construction and cycle prefix sums
class BlockTree:
    def __init__(self, adj):
        self.adj = adj  # dict: u -> list of (v, w)
        self.N = max(adj.keys()) + 1 if adj else 0

        # To be filled:
        self.bt_adj = []          # adjacency list of block-tree
        self.bt_weight = {}       # (u,v) -> weight on block-tree edge
        self.vert2block = {}      # original vertex -> block-tree node index
        self.index2node = []      # list of ('A', u) or ('B', bcc_index)
        self.is_cycle = []        # for each BCC index
        self.bridge_weight = []   # for each BCC index
        self.cycle_order = []     # for each BCC: list of vertices in cycle order
        self.cycle_pos = []       # for each BCC: dict v->pos in cycle_order
        self.cycle_split = []     # for each BCC: split index j
        self.cycle_pref1 = []     # for each BCC: prefix sums for chain1
        self.cycle_pref2 = []     # for each BCC: prefix sums for chain2

        self.build()

    def build(self):
        # 1. Edge-BCCs
        bccs = edge_bcc(self.adj)  # list of list of (u,v)
        B = len(bccs)
        # 2. vertex_bccs
        vertex_bccs = defaultdict(list)
        for i, comp in enumerate(bccs):
            for u, v in comp:
                vertex_bccs[u].append(i)
                vertex_bccs[v].append(i)
        # remove duplicates
        for u in list(vertex_bccs.keys()):
            vertex_bccs[u] = list(set(vertex_bccs[u]))
        # 3. articulation vertices
        isArt = {u for u, bl in vertex_bccs.items() if len(bl) > 1}
        # 4. assign indices: articulation nodes first, then BCC nodes
        artIndex = {}
        idx = 0
        for u in sorted(isArt):
            artIndex[u] = idx
            self.index2node.append(('A', u))
            idx += 1
        bccIndex = {}
        for i in range(B):
            bccIndex[i] = idx
            self.index2node.append(('B', i))
            idx += 1
        BTN = idx
        # init adjacency
        self.bt_adj = [[] for _ in range(BTN)]
        # 5. BCC vertices list
        bcc_vertices = []
        for comp in bccs:
            vs = set()
            for u, v in comp:
                vs.add(u); vs.add(v)
            bcc_vertices.append(list(vs))
        # 6. Build block-tree edges
        for i in range(B):
            bi = bccIndex[i]
            for u in bcc_vertices[i]:
                if u in isArt:
                    ai = artIndex[u]
                    self.bt_adj[bi].append(ai)
                    self.bt_adj[ai].append(bi)
        # 7. vert2block mapping
        for u in range(self.N):
            if u in isArt:
                self.vert2block[u] = artIndex[u]
            else:
                blist = vertex_bccs.get(u, [])
                if blist:
                    self.vert2block[u] = bccIndex[blist[0]]
                else:
                    self.vert2block[u] = None
        # 8. Determine cycle vs bridge for each BCC, and set weights on block-tree edges
        self.is_cycle = [False]*B
        self.bridge_weight = [0]*B
        for i in range(B):
            comp = bccs[i]
            if len(comp) == 1:
                # bridge-block
                u, v = comp[0]
                wval = None
                for x, w in self.adj[u]:
                    if x == v:
                        wval = w; break
                if wval is None:
                    wval = 1
                self.is_cycle[i] = False
                self.bridge_weight[i] = wval
                bi = bccIndex[i]
                for endpoint in (u, v):
                    if endpoint in isArt:
                        ai = artIndex[endpoint]
                        self.bt_weight[(bi, ai)] = wval
                        self.bt_weight[(ai, bi)] = wval
            else:
                deg = defaultdict(int)
                for u, v in comp:
                    deg[u] += 1; deg[v] += 1
                cyc = all(deg[u] == 2 for u in deg)
                if cyc:
                    self.is_cycle[i] = True
                else:
                    self.is_cycle[i] = False
                bi = bccIndex[i]
                for u in bcc_vertices[i]:
                    if u in isArt:
                        ai = artIndex[u]
                        # weight zero for cycle entry/exit
                        self.bt_weight[(bi, ai)] = 0
                        self.bt_weight[(ai, bi)] = 0
        # 9. For cycle-blocks: build cycle_order, pos, split, prefix sums
        self.cycle_order = [None]*B
        self.cycle_pos = [None]*B
        self.cycle_split = [None]*B
        self.cycle_pref1 = [None]*B
        self.cycle_pref2 = [None]*B
        for i in range(B):
            if not self.is_cycle[i]:
                continue
            verts = bcc_vertices[i]
            subadj = defaultdict(list)
            for u, v in bccs[i]:
                subadj[u].append(v)
                subadj[v].append(u)
            start = verts[0]
            order = []
            prev = -1; cur = start
            while True:
                order.append(cur)
                nxt = None
                for w in subadj[cur]:
                    if w != prev:
                        nxt = w; break
                if nxt is None or nxt == start:
                    break
                prev, cur = cur, nxt
            k = len(order)
            self.cycle_order[i] = order
            pos_map = {order[idx]: idx for idx in range(k)}
            self.cycle_pos[i] = pos_map
            j = k // 2
            self.cycle_split[i] = j
            # prefix1 for chain1 [0..j]
            pref1 = [0]*(j+1)
            for t in range(1, j+1):
                u0 = order[t-1]; u1 = order[t]
                wval = 1
                for x, w in self.adj[u0]:
                    if x == u1:
                        wval = w; break
                pref1[t] = pref1[t-1] + wval
            self.cycle_pref1[i] = pref1
            # prefix2 for chain2: indices 0..(k-j)
            len2 = k - j + 1
            pref2 = [0]*len2
            for t in range(1, len2):
                prev_v = order[0] if t==1 else order[k-(t-1)]
                cur_v = order[k-t]
                wval = 1
                for x, w in self.adj[prev_v]:
                    if x == cur_v:
                        wval = w; break
                pref2[t] = pref2[t-1] + wval
            self.cycle_pref2[i] = pref2

    # Query sum within cycle-block i between vertices u and v per paper convention
    def query_cycle(self, i, u, v):
        order = self.cycle_order[i]
        pos_map = self.cycle_pos[i]
        j = self.cycle_split[i]
        pref1 = self.cycle_pref1[i]
        pref2 = self.cycle_pref2[i]
        k = len(order)
        iu = pos_map[u]; iv = pos_map[v]
        if iu <= j and iv <= j:
            lo, hi = min(iu, iv), max(iu, iv)
            return pref1[hi] - pref1[lo]
        iu2 = k - iu; iv2 = k - iv
        if iu2 <= (k - j) and iv2 <= (k - j):
            lo, hi = min(iu2, iv2), max(iu2, iv2)
            return pref2[hi] - pref2[lo]
        res = 0
        if iu <= j:
            res += pref1[iu]
        else:
            res += pref2[k - iu]
        if iv <= j:
            res += pref1[iv]
        else:
            res += pref2[k - iv]
        return res

# Heavy-Light Decomposition on tree (block-tree)
class HLD:
    def __init__(self, adj, bt_weight, index2node):
        self.N = len(adj)
        self.adj = adj
        self.bt_weight = bt_weight
        self.index2node = index2node
        self.parent = [-1]*self.N
        self.depth = [0]*self.N
        self.size = [0]*self.N
        self.heavy = [-1]*self.N
        self.head = [0]*self.N
        self.pos = [0]*self.N
        self.cur = 0
        self.segN = 1
        self.seg = []
        if self.N > 0:
            self.build(0)

    def dfs(self, u, p):
        self.parent[u] = p
        self.size[u] = 1
        maxsz = 0
        for v in self.adj[u]:
            if v == p: continue
            self.depth[v] = self.depth[u] + 1
            self.dfs(v, u)
            if self.size[v] > maxsz:
                maxsz = self.size[v]
                self.heavy[u] = v
            self.size[u] += self.size[v]

    def decompose(self, u, h):
        self.head[u] = h
        self.pos[u] = self.cur; self.cur += 1
        if self.heavy[u] != -1:
            self.decompose(self.heavy[u], h)
        for v in self.adj[u]:
            if v == self.parent[u] or v == self.heavy[u]: continue
            self.decompose(v, v)

    def build(self, root=0):
        self.dfs(root, -1)
        self.decompose(root, root)
        while self.segN < self.N: self.segN *= 2
        self.seg = [0]*(2*self.segN)
        base = [0]*self.N
        for u in range(self.N):
            p = self.parent[u]
            if p != -1:
                w = self.bt_weight.get((u, p), 0)
                base[self.pos[u]] = w
        for i in range(self.N):
            self.seg[self.segN + i] = base[i]
        for i in range(self.segN-1, 0, -1):
            self.seg[i] = self.seg[2*i] + self.seg[2*i+1]

    def query_seg(self, l, r):
        if l > r:
            return 0
        res = 0
        l += self.segN; r += self.segN
        while l <= r:
            if (l & 1) == 1:
                res += self.seg[l]; l += 1
            if (r & 1) == 0:
                res += self.seg[r]; r -= 1
            l //= 2; r //= 2
        return res

    def query(self, u, v):
        res = 0
        while self.head[u] != self.head[v]:
            if self.depth[self.head[u]] > self.depth[self.head[v]]:
                hu = self.head[u]
                res += self.query_seg(self.pos[hu], self.pos[u])
                u = self.parent[hu]
            else:
                hv = self.head[v]
                res += self.query_seg(self.pos[hv], self.pos[v])
                v = self.parent[hv]
        if u == v:
            return res
        if self.depth[u] > self.depth[v]:
            res += self.query_seg(self.pos[v]+1, self.pos[u])
        else:
            res += self.query_seg(self.pos[u]+1, self.pos[v])
        return res

    def lca(self, u, v):
        while self.head[u] != self.head[v]:
            if self.depth[self.head[u]] > self.depth[self.head[v]]:
                u = self.parent[self.head[u]]
            else:
                v = self.parent[self.head[v]]
        return u if self.depth[u] < self.depth[v] else v

# C–HLD query combining block-tree HLD and cycle queries
def query_c_hld(u, v, adj, BT, hld):
    Bu = BT.vert2block.get(u, None)
    Bv = BT.vert2block.get(v, None)
    if Bu is None or Bv is None:
        return 0
    if Bu == Bv:
        typ, val = hld.index2node[Bu]
        if typ == 'A':
            return 0
        else:
            i = val
            if BT.is_cycle[i]:
                return BT.query_cycle(i, u, v)
            else:
                # bridge-block: check direct edge
                for x, w in adj[u]:
                    if x == v:
                        return w
                return 0
    w = hld.lca(Bu, Bv)
    path1 = []
    x = Bu
    while x != w:
        path1.append(x)
        x = hld.parent[x]
    path1.append(w)
    path2 = []
    x = Bv
    while x != w:
        path2.append(x)
        x = hld.parent[x]
    full = path1 + path2[::-1]
    total = 0
    in_cycle = False
    cycle_i = None
    entry_vertex = None
    for idx in range(len(full)-1):
        P = full[idx]; Q = full[idx+1]
        typP, valP = hld.index2node[P]
        typQ, valQ = hld.index2node[Q]
        if typP == 'A' and typQ == 'B':
            i = valQ
            if BT.is_cycle[i]:
                in_cycle = True
                cycle_i = i
                entry_vertex = valP
            else:
                total += BT.bridge_weight[i]
        elif typP == 'B' and typQ == 'A':
            i = valP
            if BT.is_cycle[i] and in_cycle and cycle_i == i:
                total += BT.query_cycle(i, entry_vertex, valQ)
                in_cycle = False
                cycle_i = None
                entry_vertex = None
            # else: leaving bridge-block, already counted on entering
        else:
            # Should not happen in a correct block-tree path
            pass
    # After traversal, if ended inside cycle-block
    last = full[-1]
    typL, valL = hld.index2node[last]
    if typL == 'B' and BT.is_cycle[valL] and in_cycle and cycle_i == valL:
        total += BT.query_cycle(valL, entry_vertex, v)
    return total

# Naive DFS path sum for comparison
def dfs_path_sum_bench(u, v, adj):
    visited = set([u])
    par = {u: None}
    q = deque([u])
    while q:
        x = q.popleft()
        if x == v:
            break
        for nei, w in adj[x]:
            if nei not in visited:
                visited.add(nei)
                par[nei] = x
                q.append(nei)
    if v not in par:
        return 0
    res = 0
    cur = v
    while par[cur] is not None:
        p = par[cur]
        for nei, w in adj[cur]:
            if nei == p:
                res += w; break
        cur = p
    return res

# Benchmarking C–HLD vs naive DFS
def benchmark(n, num_queries=100):
    adj = generate_cactus(n)
    vertices = list(adj.keys())
    if not vertices:
        return None
    # Build block-tree and HLD
    BT = BlockTree(adj)
    BTN = len(BT.bt_adj)
    # Build HLD on block-tree
    hld = HLD(BT.bt_adj, BT.bt_weight, BT.index2node)
    # Generate queries
    queries = [(random.choice(vertices), random.choice(vertices)) for _ in range(num_queries)]
    # Time C–HLD queries
    t0 = time.perf_counter()
    for u, v in queries:
        _ = query_c_hld(u, v, adj, BT, hld)
    t1 = time.perf_counter()
    c_time = (t1 - t0) * 1000
    # Time naive DFS queries (only small n feasible)
    dfs_time = None
    if n <= 500:
        t2 = time.perf_counter()
        for u, v in queries:
            _ = dfs_path_sum_bench(u, v, adj)
        t3 = time.perf_counter()
        dfs_time = (t3 - t2) * 1000
    return c_time, dfs_time

if __name__ == "__main__":
    # Run benchmark for sizes up to 500
    sizes = [100, 200, 300, 400, 500]
    print("n, C-HLD_query_total_ms, DFS_query_total_ms")
    for n in sizes:
        res = benchmark(n, num_queries=100)
        if res:
            c_time, dfs_time = res
            dfs_report = f"{dfs_time:.2f}" if dfs_time is not None else "N/A"
            print(f"{n}, {c_time:.2f}, {dfs_report}")
