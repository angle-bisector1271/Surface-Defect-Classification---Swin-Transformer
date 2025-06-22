
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

def dfs_path_sum(u, v, adj):
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

def benchmark(n, num_queries=100):
    adj = generate_cactus(n)
    vertices = list(adj.keys())
    if not vertices:
        return None
    queries = [(random.choice(vertices), random.choice(vertices)) for _ in range(num_queries)]
    t0 = time.perf_counter()
    for u, v in queries:
        _ = dfs_path_sum(u, v, adj)
    t1 = time.perf_counter()
    dfs_time = (t1 - t0) * 1000
    return dfs_time

# Run benchmark for small sizes
results = []
for n in [100, 200, 300, 400, 500]:
    trials = 3
    dfs_times = []
    for _ in range(trials):
        res = benchmark(n, num_queries=100)
        if res:
            dfs_times.append(res)
    if dfs_times:
        avg_dfs = sum(dfs_times)/len(dfs_times)
        results.append({'n': n, 'DFS_query_total_ms': avg_dfs})

# Print results
for row in results:
    print(row)
