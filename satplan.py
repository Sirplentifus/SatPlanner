from encode import *;
from SAT_solver import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(3);

SAT_save(ThisProblem.Total_Statement, 'SAT.dat');

print(ThisProblem);

#~ XOR_Problem = SAT_Sentence();
#~ XOR_Problem.N_Vars = 2;
#~ XOR_Problem.Clauses = [[Literal(0,True), Literal(1,True)], [Literal(0,False), Literal(1,False)]];

Solver = SAT_solver(ThisProblem.Total_Statement);
Solver.Solve();

#~ Solver.Assignments[21] = True;
#~ Solver.Assignments[22] = True;
#~ Solver.Assignments[27] = True;

#~ Solver.Assignments[54] = True;
#~ Solver.Assignments[57] = True;
#~ Solver.Assignments[62] = True;
#~ Solver.Assignments[64] = True;

#~ Solver.Assignments[88] = True;
#~ Solver.Assignments[92] = True;
#~ Solver.Assignments[97] = True;
#~ Solver.Assignments[99] = True;

SAT_save(Solver.SAT_problem, 'SAT_problem.dat');


ass_print (Solver.Assignments);


print ('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));


