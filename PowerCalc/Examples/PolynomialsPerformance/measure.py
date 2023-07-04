#!/usr/bin/env python3
import subprocess
import csv
import tqdm
import resource

tests = ["TwoGuided", "TwoManual", "TwoSimp", "TwoUnguided"]
num_runs = 10
warmup = 2
time_limit = 60 #minutes
mem_limit = 8 #GB

def run_test(test):
    cmd = f"(cd ../../../; lake build PowerCalc.Examples.PolynomialsPerformance.{test})"
    res = subprocess.run(cmd, shell=True, capture_output=True)
    return res

def gb_to_b(b):
    return int(b * 1024 * 1024 * 1024)

def min_to_sec(m):
    return int(m * 60)

def benchmark_test(test, warmup, num_runs):
  res = []
  print(f"Running {test}... (warmup)")
  for _ in tqdm.tqdm(range(warmup)):
    run_test(test)
  print(f"Benchmarking {test}...")
  for _ in tqdm.tqdm(range(num_runs)):
    start = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
      run_test(test)
    except: #what's the correct error here?
      res.append({ 'time' : min_to_sec(time_limit), 'mem' : gb_to_b(mem_limit)})
      continue
    end = resource.getrusage(resource.RUSAGE_CHILDREN)
    res.append({ 'time' : end.ru_utime - start.ru_utime, 'mem' : end.ru_maxrss - start.ru_maxrss })
  return res

def main(tests, warmup, num_runs):
    with open('results.csv', 'w') as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["Test", "Time", "Memory"])
        for t in tests:
            res = benchmark_test(t, warmup, num_runs)
            for r in res:
                csv_writer.writerow([t, r['time'], r['mem']])

if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (gb_to_b(mem_limit) - 1, gb_to_b(mem_limit)))
    resource.setrlimit(resource.RLIMIT_CPU, (min_to_sec(time_limit) - 1, min_to_sec(time_limit)))
    main(tests, warmup, num_runs)
