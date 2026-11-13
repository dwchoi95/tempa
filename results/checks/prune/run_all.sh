#!/bin/zsh
# Run every (assignment, builder) job, 8 at a time; rerun to resume after a reboot.
cd "$(dirname $0)/../../.."
mkdir -p results/checks/prune/logs
xargs -P 8 -L 1 zsh -c 'python3 results/checks/prune/run.py $0 $1 > results/checks/prune/logs/$0__$1.log 2>&1' < results/checks/prune/jobs.txt
echo all done
