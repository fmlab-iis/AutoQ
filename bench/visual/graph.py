import csv
import matplotlib.pyplot as plt
import re
import tabulate
import sys
import statistics

# max min median priemer win/lose odchylka

x = []
y = []
count_x = 0
count_y = 0

iny_win = 0
rt_win = 0

iny_priemer = 0
rt_priemer = 0

if (len(sys.argv) != 3):
    print("graph.py vertical_bench horizontal_bench")
    sys.exit()

csvfile = open('../bench_results/result_brzozowski.csv', 'r')
csvfile2 = open('../bench_results/result_residuals.csv', 'r')
plots = csv.reader(csvfile, delimiter = ';')
plots2 = csv.reader(csvfile2, delimiter = ';')

for row in plots:
    if (row[0] == 'name'):
        continue
    if (row[3] == 'TO'):
        row[3] = '60'
    if (row[3] == 'ERR'):
        row[3] = '60'
    count_x = count_x + 1

    x.append(float(row[3]));

for row in plots2:
    if (row[0] == 'name'):
        continue
    if (row[3] == 'TO'):
        row[3] = '60'
    if (row[3] == 'ERR'):
        row[3] = '60'
    count_y = count_y + 1

    y.append(float(row[3]));
#    match = re.match(r'([a-z]*)\/b-([a-z-]*)\/(aut[0-9]*)', row[0])
#    x.append('{0},{1}'.format(match[2], match[3]))
#    y.append(float(row[3]))

if (count_x != count_y):
    print("exiting")
    sys.exit()

for i in range(0, count_x):
    if (x[i] < y[i]):
        iny_win = iny_win + 1
    if (x[i] > y[i]):
        rt_win = rt_win + 1
    iny_priemer = iny_priemer + x[i]
    rt_priemer = rt_priemer + y[i]

iny_priemer = iny_priemer / (i + 1)
rt_priemer = rt_priemer / (i + 1)

max_x = max(x)
min_x = min(x)

max_y = max(y)
min_y = min(y)

iny_median = statistics.median(x) 
rt_median = statistics.median(y) 

iny_stddev = statistics.stdev(x)
rt_stddev = statistics.stdev(y)

data = [
    {"Algorithm": sys.argv[1], "Max": max_x, "Min": min_x, "Median": iny_median, "Stddev": iny_stddev, "Mean": iny_priemer, "Wins": iny_win },
    {"Algorithm": sys.argv[2], "Max": max_y, "Min": min_y, "Median": rt_median, "Stddev": rt_stddev, "Mean": rt_priemer, "Wins": rt_win }
]

table = tabulate.tabulate(data,headers = "keys", tablefmt="pipe",colalign=("left", "center", "right"),missingval = "N/A")

# Printing the table
print(table)

plt.scatter(x, y, color = 'g',s = 50)
plt.xlabel(sys.argv[1]) 
plt.ylabel(sys.argv[2]) 
plt.xscale("log") 
plt.yscale("log") 
plt.title('Lstar Scatter plot', fontsize = 20) 
plt.grid(True)
plt.axis('square')

line = plt.axline((0,0),(60,60))
line.set_dashes([5,2,1,2])
line.set_color('gray')

line = plt.axline((60,0),(60,60))
line.set_dashes([5,2,1,2])
line.set_color('gray')

line = plt.axline((0,60),(60,60))
line.set_dashes([5,2,1,2])
line.set_color('gray')

plt.savefig("plot.png")