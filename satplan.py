import sys;

from encoder import *;
from SAT_defs import *

from SAT_solver_VSIDS import *; #Choose between SAT_solver_VSIDS, SAT_solver_heur, or SAT_solver. SAT_solver_VSIDS is the fastest solver we've made

DEBUG = True; #If true, produces certain output to stdout and to files in folder Dump (must exist)    

fh = open(sys.argv[1],'r');    
#Initializing the problem (Reads the file fh, and prepares the encoding)
ThisProblem = problem(fh);

if(DEBUG):
    #Prints the data gathered by problem.
    print(ThisProblem);
    
    #Prints to file the statements. Useful in debugging and to find possible improvements
    SAT_save(ThisProblem.Init_Statement, './Dump/Init_Statement.dat');
    SAT_save(ThisProblem.Goal_Statement, './Dump/Goal_Statement.dat');
    SAT_save(ThisProblem.Actions_Statement, './Dump/Actions_Statement.dat');
    SAT_save(ThisProblem.Frame_Statement, './Dump/Frame_Statement.dat');
    SAT_save(ThisProblem.Exclusive_Statement, './Dump/Exclusive_Statement.dat');
    

#In this loop we iteratively increase the horizon until a solution to the
#problem is found, or the horizon exceeds a certain value, after which
#We give up and consider the problem unsolvable.
Solved = False;
for horz in range(1,15):
    if(DEBUG):
        print('Now trying h=%d'%horz);
    ThisProblem.set_horizon(horz);

    Solver = SAT_solver(ThisProblem.Total_Statement);
    
    if(Solver.Solve()):
        Solved = True;
        break;

if(DEBUG):
    SAT_save(ThisProblem.Total_Statement, './Dump/SAT.dat');
    print('');
    
    
if(Solved):
    #Decoding the assignments into the requested output format
    print (ThisProblem.decode_assignment(Solver.Assignments));
else:
    print('Could not solve the problem');


