from os import listdir
from os.path import isfile, join
import pdb
import time

from encoder import *

#Choose between SAT_solver_VSIDS, SAT_solver_heur, or SAT_solver. 
# SAT_solver_VSIDS is the fastest solver we've made
from SAT_solver_VSIDS import *
#from SAT_solver import *

TestsFolder = './Tests/'

File_Names = [f for f in listdir(TestsFolder) if isfile(join(TestsFolder, f))]

for file_name in File_Names:
    
    print('Testing problem %s\n'%file_name)
    
    t = time.time()
    
    fh = open(TestsFolder+file_name,'r')
    ThisProblem = problem(fh)
    
    print('Initial encoding time: %.1f\n'%(time.time() - t))
    
    t = time.time()

    Solved = False
    
    for horz in range(1,15):
        ThisProblem.set_horizon(horz)
        Solver = SAT_solver(ThisProblem.Total_Statement)
        if(Solver.Solve()):
            Solved = True
            break
    
    if(Solved):
        print('Problem solved:')
        print('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments))
    else:
        print('Problem could not be solved\n')

    print('Solution time: %.1f\n'%(time.time() - t))
    
