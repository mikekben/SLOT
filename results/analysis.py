import csv
import argparse
import statistics
from prettytable import PrettyTable

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', '--file',
                        help='Input statistics file',
                        required=True)
    args = parser.parse_args()
    return args


class Entry:
    def __init__(self, arr):
        self.arr = arr
    
    def name(self):
        return self.arr[0]
    
    def result(self, solver, isPre):
        n = 0 if isPre else 2
        if solver == 'z':
            return self.arr[1+n]
        elif solver == 'c':
            return self.arr[5+n]
        elif solver == 'b':
            return self.arr[9+n]
        
    def solTime(self, solver, isPre):
        n = 0 if isPre else 2
        if solver == 'z':
            if (not isPre) and (self.arr[2+n] ==''):
                return 600 #SLOT timeout
            else:
                return max(float(self.arr[2+n]), 0.005)
        elif solver == 'c':
            if (not isPre) and (self.arr[6+n] ==''):
                return 600 #SLOT timeout
            else:
                return max(float(self.arr[6+n]), 0.005)
        elif solver == 'b':
            if (not isPre) and (self.arr[10+n] ==''):
                return 600 #SLOT timeout
            else:
                return max(float(self.arr[10+n]), 0.005)

    def isSlotTimeout(self):
        return len(self.arr) < 16 
    
    def frontTime(self):
        #print(self.arr)
        return 0 if self.isSlotTimeout() else float(self.arr[23])
    def optTime(self):
        return 0 if self.isSlotTimeout() else float(self.arr[24])
    def backTime(self):
        return 0 if self.isSlotTimeout() else float(self.arr[25])
    
    def slotTime(self):
        return 600 if self.isSlotTimeout() else self.frontTime()+self.optTime()+self.backTime()

    def usedPass(self, n):
        return (not self.isSlotTimeout()) and (self.arr[26+n] == '1')
    
    def finalTime(self, solver):
        return self.solTime(solver, False)+self.frontTime()+self.optTime()+self.backTime()
    
    def ratio(self, solver):
        return self.solTime(solver, True)/self.finalTime(solver)
    
    def portfolioRatio(self, solver):
        return max(self.ratio(solver), 1)
    
    def inRange(self, solver, range):
        if (type(range) == int or type(range) == float):
            return self.solTime(solver, True) >= range
        else:
            return (self.solTime(solver, True) >= range[0]) and (self.solTime(solver, True) < range[1])

    def isImp(self, solver, time):
        if (type(solver) == list):
            return all([self.solTime(s, True) >= time for s in solver]) and any([self.finalTime(s) < time for s in solver])
        else:
            return (self.solTime(solver, True) >= time) and (self.finalTime(solver) < time)
        
    def isTimeout(self, solver, time):
        if (type(solver) == list):
            return all([self.solTime(s, True) >= time for s in solver])
        else:
            return (self.solTime(solver, True) >= time)



data=[]
args = parse_args()

with open(args.file, newline='') as file:

    reader = csv.reader(file, delimiter=',')

    for row in reader:
        data.append(Entry(row))

def flatten(l):
    return [item for sublist in l for item in sublist]

def count(solver, range):
    return len(list(filter(lambda x: x.inRange(solver, range), data)))

def countImp(solver, time):
    return len(list(filter(lambda x: x.isImp(solver, time), data)))

def countTimeout(solver, time):
    return len(list(filter(lambda x: x.isTimeout(solver, time), data)))

def geomeanSpeedup(solver, range, isPortfolio):
    lst = list(map(lambda x: x.portfolioRatio(solver) if isPortfolio else x.ratio(solver), filter(lambda x: x.inRange(solver, range), data)))
    if (len(lst) > 0):
        return statistics.geometric_mean(lst)
    else:
        return None
    
def averageSpeedup(solver, range, isPortfolio):
    lst = list(map(lambda x: x.portfolioRatio(solver) if isPortfolio else x.ratio(solver), filter(lambda x: x.inRange(solver, range), data)))
    if (len(lst) > 0):
        return statistics.mean(lst)
    else:
        return None
    
def usedCount(passid, solver, tm):
    if solver and tm:
        return len(list(filter(lambda x: x.usedPass(passid) and x.inRange(solver, tm), data)))
    else:
        return len(list(filter(lambda x: x.usedPass(passid), data)))

def geomeanPassSpeedup(solver, passid, tm, isPortfolio):
    lst = list(map(lambda x: x.portfolioRatio(solver) if isPortfolio else x.ratio(solver), filter(lambda x: x.usedPass(passid) and x.inRange(solver, tm), data)))
    if (len(lst) == 0):
        return None
    else:
        return statistics.geometric_mean(lst)

def geomeanWithoutPassSpeedup(solver, passid, tm, isPortfolio):
    lst = list(map(lambda x: x.portfolioRatio(solver) if isPortfolio else x.ratio(solver), filter(lambda x: (not x.usedPass(passid)) and x.inRange(solver, tm), data)))
    if (len(lst) == 0):
        return None
    else:
        return statistics.geometric_mean(lst)
    


def averagePassSpeedup(solver, passid, tm, isPortfolio):
    lst = list(map(lambda x: x.portfolioRatio(solver) if isPortfolio else x.ratio(solver), filter(lambda x: x.usedPass(passid) and x.inRange(solver, tm), data)))
    if (len(lst) == 0):
        return None
    else:
        return statistics.mean(lst)
    
def slotpost(solver, range):
    return statistics.geometric_mean(list(map(lambda x: x.slotTime()/x.finalTime(solver), filter(lambda x: x.inRange(solver, range), data))))

def frontaverage():
    return statistics.geometric_mean(list(map(lambda x: x.frontTime()/x.slotTime(), filter(lambda x: (not x.isSlotTimeout()), data))))

def optaverage():
    return statistics.geometric_mean(list(map(lambda x: x.optTime()/x.slotTime(), filter(lambda x: (not x.isSlotTimeout()), data))))

def backaverage():
    return statistics.geometric_mean(list(map(lambda x: x.backTime()/x.slotTime(), filter(lambda x: (not x.isSlotTimeout()), data))))



# Specify the Column Names while initializing the Table


if ("bv" in args.file) and (not "bvfp" in args.file):
    allSolvers = ['z', 'c', 'b']
else:
    allSolvers = ['z', 'c']

for s in allSolvers:
    print(s)
    myTable = PrettyTable(["Interval", "Count", "SLOT-only geomean", "Portfolio geomean"])

    for r in [(0,30), (30,60), (60,120), (120,300), 300]:
        myTable.add_row([str(r), str(count(s, r)), str(round(geomeanSpeedup(s, r, False), 2)), str(round(geomeanSpeedup(s, r, True), 2))])

    print(myTable)


tos = [30, 60, 120, 300, 600]
myTable = PrettyTable(["     "] + list(map(lambda x: "sol " + x, allSolvers)) + ["all"])
for r in [30, 60, 120, 300, 600]:
    myTable.add_row([str(r)+" total"] + [str(countTimeout(s, r)) for s in allSolvers] + [str(countTimeout(allSolvers, r))])
    myTable.add_row([str(r)+" imp"] + [str(countImp(s, r)) for s in allSolvers] + [str(countImp(allSolvers, r))])
    myTable.add_row([str(r)+" %"] + [str(round(100*countImp(s, r)/countTimeout(s, r), 2)) for s in allSolvers] + [str(round(100*countImp(allSolvers, r)/countTimeout(allSolvers, r), 2))])

print(myTable)

print("Total: " + str(len(data)))
passes = ["instcombine", "ainstcombine", "reassociate", "sccp", "dce", "adce", "instsimplify", "gvn"]


for tm in [0, 30, 300, 600]:
    myTable = PrettyTable(["Pass", "Used Count", "%", "speedup with", "speedup without"])
    print(f"In range ({tm}): " + str(count('z', tm)))
    n = 0




    for i in range(len(passes)):
        myTable.add_row([passes[i], str(usedCount(i, 'z', tm)), str(round(100*usedCount(i, 'z', tm)/count('z', tm), 2)), \
                        #str(round(geomeanPassSpeedup('z', i, 0, True), 2) if geomeanPassSpeedup('z', i, 0, True) else '-'), \
                        #str(round(geomeanWithoutPassSpeedup('z', i, 0, True), 2) if geomeanWithoutPassSpeedup('z', i, 0, True) else '-'), \
                        str(round(geomeanPassSpeedup('z', i, tm, True), 2) if geomeanPassSpeedup('z', i, tm, True) else '-'), \
                        str(round(geomeanWithoutPassSpeedup('z', i, tm, True), 2) if geomeanWithoutPassSpeedup('z', i, tm, True) else '-')])

    print(myTable)


for r in [(0,30), (30,60), (60,120), (120,300), 300]:
    print(f"{r} : {round(100*slotpost('z', r),2)}")


print(frontaverage())
print(optaverage())
print(backaverage())
    #print(s + " " + str(r) + "   " + str(countTimeout(s, r)) + "   " + str(countImp(s, r)))

#for r in [30, 60, 120, 300, 600]:
#    print("all" + " " + str(r) + "   " + str(countTimeout(allSolvers, r)) + "   " + str(countImp(allSolvers, r)))


#bv 
#0.5951222387386229
#0.10710224347359946
#0.053089776125046076

#bvfp
#0.30546484370053445
#0.0704644619075241
#0.5986981787552723

#fp
#0.34238276547630403
#0.07923041627326863
#0.5732070251353116




#print(statistics.geometric_mean(list(map(lambda x: x.ratio('z'), filter(lambda x: x.inRange('z', 300), data)))))

#print(list(filter(lambda x: x.inRange('z', 300), data)))