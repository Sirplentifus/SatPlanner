from os import listdir;
from os.path import isfile, join;
import pdb;
import time;

from encode import *;
from SAT_solver_heur import *;

TestsFolder = './Tests/';

File_Names = [f for f in listdir(TestsFolder) if isfile(join(TestsFolder, f))]

for file_name in File_Names:
    
    print('Testing problem %s\n'%file_name);
    
    t = time.time();
    
    fh = open(TestsFolder+file_name,'r');
    ThisProblem = problem(fh);
    
    print('Initial encoding time: %.1f\n'%(time.time() - t));
    
    t = time.time();

    Solved = False;
    horz = 1;
    while(horz<5):
        ThisProblem.set_horizon(horz);
        Solver = SAT_solver_heur(ThisProblem.Total_Statement);
        if(Solver.Solve()):
            Solved = True;
            break;
        else:
            horz+=1;   
    
    if(Solved):
        print('Problem solved:');
        print('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));
    else:
        print('Problem could not be solved\n');
    
    print('Solution time: %.1f\n'%(time.time() - t));
    
