from encode import *;
from SAT_solver import *;
import pdb;

DEBUG = False;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);


Solved = True;
horz = 1;
while(horz<5):
    ThisProblem.set_horizon(horz);
    Solver = SAT_solver(ThisProblem.Total_Statement);
    if(Solver.Solve()):
        Solved = True;
        break;
    else:
        horz+=1;

if(DEBUG):
    print(ThisProblem);

    SAT_save(ThisProblem.Init_Statement, './Dump/Init_Statement.dat');
    SAT_save(ThisProblem.Goal_Statement, './Dump/Goal_Statement.dat');
    SAT_save(ThisProblem.Actions_Statement, './Dump/Actions_Statement.dat');
    SAT_save(ThisProblem.Frame_Statement, './Dump/Frame_Statement.dat');
    SAT_save(ThisProblem.Exclusive_Statement, './Dump/Exclusive_Statement.dat');
    SAT_save(ThisProblem.Total_Statement, './Dump/SAT.dat');
    
    
    



if(Solved):
    print('Problem solved:');
    print ('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));
else:
    print('Problem is unsolvable');


