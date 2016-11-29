from encode import *;
from SAT_solver import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(3);

print(ThisProblem);
print('\tTotal_Statement: %s\n'%( ThisProblem.Total_Statement));

#~ XOR_Problem = SAT_Sentence();
#~ XOR_Problem.N_Vars = 2;
#~ XOR_Problem.Clauses = [[Literal(0,True), Literal(1,True)], [Literal(0,False), Literal(1,False)]];

Solver = SAT_solver(ThisProblem.Total_Statement);
#~ Solver = SAT_solver(XOR_Problem);
Solver.Solve();

print ('%s'%Solver.SAT_problem);
print ('%s'%Solver.Assignments);
print ('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));

#~ pdb.set_trace();
