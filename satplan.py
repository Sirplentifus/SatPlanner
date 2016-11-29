from encode import *;
from SAT_solver import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);

print(ThisProblem);

Solved = False;
horz = 1;
while(horz<5):
    ThisProblem.set_horizon(horz);
    Solver = SAT_solver(ThisProblem.Total_Statement);
    if(Solver.Solve()):
        Solved = True;
        break;
    else:
        horz+=1;

SAT_save(ThisProblem.Total_Statement, 'SAT.dat');


if(Solved):
    print('Problem solved:');
    print ('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));
else:
    print('Problem is unsolvable');


