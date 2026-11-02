"""Usage: python3 enumerate_graphs.py [-b] <n> [<workers>=1] [<threshold>=1]
Output: the smallest ratio below threshold on at most n vertices (bipartite if -b)
and a witnessing graph, or No solution.
Uses floating-point greedy screening and exact DP for the remaining candidates.
Requires nauty-geng, pynauty, and a compiled greedy_filter beside this file.
"""
import subprocess
import sys
from concurrent.futures import Future, ProcessPoolExecutor, ThreadPoolExecutor
from fractions import Fraction
from heapq import heappop, heappush
from multiprocessing import get_context
from pathlib import Path
from queue import Queue

from opt import ratio

GENG = "nauty-geng"
FILTER = str(Path(__file__).with_name("greedy_filter"))


def read_graph6(line):
    line = line.strip()
    n = ord(line[0]) - 63
    bits = (ord(c) - 63 >> shift & 1 for c in line[1:] for shift in range(5, -1, -1))
    return n, [(u, v) for v in range(1, n) for u in range(v) if next(bits)]


def screen(n, part, workers, answer, events, bipartite=False):
    cmd = [GENG, "-q", "-g"] + (["-b"] if bipartite else []) + [str(n), "1:0", f"{part}/{workers}"]
    try:
        with subprocess.Popen(cmd, stdout=subprocess.PIPE) as geng:
            with subprocess.Popen([FILTER, str(float(answer))], stdin=geng.stdout,
                                  stdout=subprocess.PIPE, text=True) as screening:
                geng.stdout.close()
                for line in screening.stdout:
                    graph, greedy = line.split()
                    events.put((float(greedy), graph))
        # Leaving both with-blocks waits for the processes, so returncodes are set.
        if geng.returncode or screening.returncode:
            raise RuntimeError(f"n={n} part={part}: geng {geng.returncode}, "
                               f"greedy_filter {screening.returncode}")
    finally:
        events.put(None)


def evaluate(graph):
    return ratio(*read_graph6(graph)), graph


def minimum_ratio(n, workers=1, threshold=1, bipartite=False):
    answer = Fraction(threshold)
    best_graph = None
    with (ProcessPoolExecutor(workers, mp_context=get_context("spawn")) as pool,
          ThreadPoolExecutor(workers) as readers):
        for k in range(2, n + 1):
            events = Queue()
            tasks = [readers.submit(screen, k, part, workers, answer, events, bipartite)
                     for part in range(workers)]
            candidates, active, pending = [], workers, 0
            while True:
                # Submit only to idle workers, smallest greedy ratio first, and recheck
                # against the current answer, which may have dropped since screening.
                while candidates and pending < workers:
                    greedy, graph = heappop(candidates)
                    if greedy <= float(answer) + 1e-6:
                        pool.submit(evaluate, graph).add_done_callback(events.put)
                        pending += 1
                if not (active or pending):
                    break
                event = events.get()
                if event is None:
                    active -= 1
                elif isinstance(event, Future):
                    value, graph = event.result()
                    if value < answer:
                        answer, best_graph = value, graph
                    pending -= 1
                else:
                    heappush(candidates, event)
            for task in tasks:
                task.result()
    return (answer, best_graph) if best_graph is not None else None


if __name__ == "__main__":
    args = sys.argv[1:]
    bipartite = False
    if args and args[0] in ("-b", "--bipartite"):
        bipartite = True
        args = args[1:]
    workers = int(args[1]) if len(args) > 1 else 1
    threshold = Fraction(args[2]) if len(args) > 2 else 1
    result = minimum_ratio(int(args[0]), workers=workers, threshold=threshold, bipartite=bipartite)
    if result is None:
        print("No solution")
    else:
        answer, graph = result
        n, edges = read_graph6(graph)
        print(answer)
        print(n, len(edges))
        for u, v in edges:
            print(u, v)
