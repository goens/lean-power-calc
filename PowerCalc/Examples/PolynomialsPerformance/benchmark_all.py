#!/usr/bin/env python3
import tqdm
import subprocess
import resource

tests = ["TwoGuided", "TwoManual", "TwoUnguided"]
num_runs = 10
warmup = 2

def benchmark_test(test, warmup, num_runs):
  res = []
  print(f"Running {test}... (warmup)")
  for _ in tqdm.tqdm(range(warmup)):
    try:
      subprocess.run(f"./measure.py {test}")
    except: #what's the correct error here?
        break #don't continue warming up if times out (don't waste time)
  print(f"Benchmarking {test}...")
  for _ in tqdm.tqdm(range(num_runs)):
    start = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
      subprocess.run(f"./measure.py {test}", check=True)
    except: #what's the correct error here?
      res.append({ 'time' : -1, 'mem' : -1, 'timeout' : True})
      continue
    end = resource.getrusage(resource.RUSAGE_CHILDREN)
    res.append({ 'time' : end.ru_utime - start.ru_utime, 'mem' : end.ru_maxrss - start.ru_maxrss, 'timeout' : False})
  return res

def main():
    with open('results.csv', 'w') as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["Test", "Time", "Memory", "Timeout"])
        for t in tests:
            res = benchmark_test(t, warmup, num_runs)
            for r in res:
                csv_writer.writerow([t, r['time'], r['mem']], r['timeout'])

if __name__ == "__main__":
    main()
