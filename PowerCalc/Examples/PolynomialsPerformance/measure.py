#!/usr/bin/env python3
import subprocess
import csv
import tqdm
import resource

tests = ["TwoGuided", "TwoManual", "TwoSimp", "TwoUnguided"]
num_runs = 10
warmup = 2

def run_test(test):
    cmd = f"(cd ../../../; lake build PowerCalc.Examples.PolynomialsPerformance.{test})"
    res = subprocess.run(cmd, shell=True, capture_output=True)
    return res

def benchmark_test(test, warmup, num_runs):
  res = []
  print(f"Running {test}... (warmup)")
  for _ in tqdm.tqdm(range(warmup)):
    run_test(test)
  print(f"Benchmarking {test}...")
  for _ in tqdm.tqdm(range(num_runs)):
    start = resource.getrusage(resource.RUSAGE_CHILDREN)
    run_test(test)
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
    main(tests, warmup, num_runs)
