import sys;
import re;
import pdb;
from collections import OrderedDict; 
import copy;

from SAT_defs import *;

class Relation: #Information about a relation in the general sense
    def __init__(self):
        self.Num_of_vars = -1;
        self.Start_Ind = -1; #Index of SAT_Variables in which the SAT_variables associated with this relation start.
    
    def __repr__(self):
        return '\tNum_of_Vars: %d\n\tStart_Ind: %d'%(self.Num_of_vars, self.Start_Ind);

class Action: #Information about an action in the general sense
    def __init__(self, Variables=None):
        self.Num_of_args = 0;
        self.Vars = []; #Variables present in definition (used to convert variables to numbers)
        
        #Lists of atoms, with variables that are numbers going from 0 to Num_of_args-1:
        self.Precond = [];
        self.Effects = [];
        
        self.Ind = -1;
        
        if(Variables != None):
            self.Vars = Variables;
            self.Num_of_args = len(Variables);
        
    def append(self, new_atom, whichset):
        
        #Converting variables to numbers
        #~ for var in new_atom.Variables:
        for i in range(len(new_atom.Variables)):
            var = new_atom.Variables[i];
            varind = [i for i in range(len(self.Vars)) if self.Vars[i]==var];
            
            if(len(varind)==0):
                pass;
            elif(len(varind)==1):
                #~ ins_atom.Variables.append(varind[0]);
                new_atom.Variables[i] = varind[0];
            else:
                raise(ValueError('Var %s was found %d times in %s'%(var, len(varind), self.Vars)));
            
        if(whichset == 'Precond'):
            self.Precond.append(new_atom);
        elif(whichset == 'Effects'):
            self.Effects.append(new_atom);
        else:
            raise(ValueError('Invalid whichset'));
        
    def __repr__(self):
        return '\tNum_of_args: %d\n\tPreconditions: %s\n\tEffects: %s\n\tInd: %d'%(self.Num_of_args, self.Precond, self.Effects, self.Ind);
        
class Atom: #Represents a specific relation or action
    def __init__(self, string):
        self.Name = '';
        self.Variables = [];
        self.affirm = None; #True if affirmed, False if negated
        
        if(not string):
            return;
        
        if(string[0] == '-'):
            self.affirm = False;
            string = string[1:];
        else:
            self.affirm = True;
        
        names = re.split('\(|,|\)', string);
        self.Name = names[0];
        for name in names[1:]: 
            if bool(name):
                self.Variables.append(name);
    
    def __repr__(self):
        
        if(self.affirm):
            S = '';
        else:
            S = '-';
        S += '%s%s'%(self.Name, self.Variables);
        return S;
#Although there are issues with using this as an action if RAA encoding is to be used...
    
class problem:
    Variables = [];
    #The order in a dict varies. Using OrderedDict instead:
    Relations = OrderedDict(); 
    Actions = OrderedDict();

    #States in the form of lists of atoms
    InitialState = []; 
    GoalState = [];
    
    #Various useful counts:
    N_vars = 0;
    N_rels = 0;
    N_acts = 0;
    N_args = 0;
    N_lits_t=0; #literals per time step (before horizon)
    N_lits = 0;
    
    h = None;
    
    def __init__(self, fileHandle=None):
        
        if(fileHandle == None):
            return;
        
        for line in fileHandle:
            if(line[0] == 'I' or line[0] == 'G'):
                
                for param in line.split()[1:]: #Consider splitting by ')' in case there are spaces in between arguments
                    this_relation = Atom(param);
                    
                    #Introduce newly found variables in self.Variables
                    for va in this_relation.Variables:
                        if(not va in self.Variables):
                            self.Variables.append(va);
                    
                    #Introduce newly found relation in self.Relations
                    aux = self.Relations.setdefault(this_relation.Name, Relation());
                    
                    if(aux.Num_of_vars != -1 and aux.Num_of_vars != len(this_relation.Variables)):
                        raise(ValueError('Number of variables used by a relation shouldn\'t change')); 
                    aux.Num_of_vars = len(this_relation.Variables);
                    
                    if(line[0] == 'I'):
                        this_relation.t = 0;
                        self.InitialState.append(this_relation);
                    elif(line[0] == 'G'):
                        #TODO h must be defined somewhere...
                        self.GoalState.append(this_relation);
                
            elif(line[0] == 'A'):
                params = line.split();
                action_atom = Atom(params[1]);
                self.Actions[action_atom.Name] = Action(action_atom.Variables);
                this_action = self.Actions[action_atom.Name];
                mode = 'Precond';
                for param in params[3:]:
                    if(param == '->'):
                        mode = 'Effects';
                        continue;
                    this_action.append(Atom(param), mode);
                #~ pdb.set_trace();
                for atm in (this_action.Precond + this_action.Effects):
                    if not atm.Name in self.Relations:
                        self.Relations[atm.Name] = Relation();
                        self.Relations[atm.Name].Num_of_vars = len(atm.Variables);
                    
                    for va in atm.Variables:
                        if isinstance(va, str) and (not va in self.Variables):
                            self.Variables.append(va);
        
        self.N_vars = len(self.Variables);
        for rel in self.Relations:
            self.Relations[rel].Start_Ind = self.N_rels;
            self.N_rels += self.N_vars**self.Relations[rel].Num_of_vars;
        
        for act in self.Actions:
            self.N_args = max(self.N_args, self.Actions[act].Num_of_args);
            self.Actions[act].Ind = self.N_rels + self.N_acts;
            self.N_acts+=1;
        self.N_lits_t = self.N_rels+self.N_acts+self.N_args*self.N_vars;
        
        #Precalculating sentences:
        self.init_statements();
        
    def init_statements(self):
        #At init all possible lits are negated, except if they're 
        #present in self.InitialState
        Lits = [Literal(i, False) for i in list(range(self.N_rels))];
        for atom in self.InitialState:
            lit = self.Rel2Lit(atom);
            Lits[lit.ID] = lit;
        #Putting in clause form
        self.Init_Statement.Clauses = [[lit] for lit in Lits];
        
        #Repeat of the previous, but for Goal state
        Lits = [Literal(i, False) for i in list(range(self.N_rels))];
        for atom in self.GoalState:
            lit = self.Rel2Lit(atom);
            Lits[lit.ID] = lit;
        self.Goal_Statement.Clauses = [[lit] for lit in Lits];
        
        #POSSIBLE IMPROVEMENT: The code below seems to generate 
        #   equal clauses, which can be excluded, and it also 
        #   generates clauses with contradicting literals that 
        #   can get resolved.
        #
        #   Also maybe skip actions with contradicting effects
        #   or preconditions... (if so, keep a list of skipped
        #   actions, to allow further improvements in frames)
        #   but first check if this doesn't break the problem.
        #   Perhaps it's best to add a clause forbidding the
        #   action.
        for act_name in self.Actions:
            act = self.Actions[act_name];
            
            #Combination of arguments seen as a number of base self.N_vars
            for arg_comb_num in range(self.N_vars**act.Num_of_args):
                args = [];
                var_inds = [];
                for arg_ordinal in range(act.Num_of_args): #Translating arg_comb_num into a list of literals and variable indexes
                    arg_var_ind = self.N_rels + self.N_acts + \
                      self.N_vars*arg_ordinal + arg_comb_num%self.N_vars;
                    
                    var_inds.append(arg_comb_num%self.N_vars);
                    args.append(Literal(arg_var_ind, False));
                    arg_comb_num//=self.N_vars;
                
                Base_Clause = [Literal(act.Ind, False)] + args;
                
                #Producing action statements
                #One clause for each precondition and effect
                for precond in act.Precond:
                    Precond_Lit = self.Rel2Lit(precond, var_inds);
                    This_Clause = Base_Clause + [Precond_Lit];
                    self.Actions_Statement.Clauses.append(This_Clause);
                for effect in act.Effects:
                    Effect_Lit = self.Rel2Lit(effect, var_inds);
                    Effect_Lit.ID += self.N_lits_t; #Effects are on the next time step
                    This_Clause = Base_Clause + [Effect_Lit];
                    self.Actions_Statement.Clauses.append(This_Clause);                    
                
                #All the relations are created, after which, the ones 
                #that are affected by this action are removed
                rel_IDs = list(range(self.N_rels));
                
                for effect in act.Effects:
                    LitID = self.Rel2Lit(effect, var_inds).ID;
                    try:
                        rel_IDs.remove(LitID);
                    except ValueError:
                        pass; # Sometimes effects get doubled
                
                #~ #Introducing the frame axioms    
                for rel_ID in rel_IDs:
                    for affirm_state in [False, True]:
                        Literal_Now = Literal(rel_ID, affirm_state);
                        Literal_After = copy.deepcopy(Literal_Now);
                        Literal_After.ID += self.N_lits_t;
                        Literal_Now.Affirm = not Literal_Now.Affirm;
                        self.Frame_Statement.Clauses.append([Literal_Now] + Base_Clause + [Literal_After]);
                
        #Exactly one action type
        At_Least_One_Clause = [Literal(i,True) for i in range(self.N_rels, self.N_rels+self.N_acts)];
        At_Most_One_Clause = [];
        for i in range(self.N_acts):
            for j in range(i+1, self.N_acts):
                At_Most_One_Clause.append( [Literal(self.N_rels+i,False), Literal(self.N_rels+j,False)] );
        self.Exclusive_Statement.Clauses += ([At_Least_One_Clause] + At_Most_One_Clause);
        
        #Exactly one kth argument
        
        At_Least_One_Clause = [Literal(self.N_rels+self.N_acts+i,True) for i in range(self.N_vars)];
        At_Most_One_Clause = [];
        for k in range(self.N_args):
            for i in range(self.N_vars):
                for j in range(i+1, self.N_vars):
                    At_Most_One_Clause.append( [Literal(self.N_rels+self.N_acts+k*self.N_vars+i,False), Literal(self.N_rels+self.N_acts+k*self.N_vars+j,False)] );
            self.Exclusive_Statement.Clauses += ([At_Least_One_Clause] + At_Most_One_Clause);           
        
    def set_horizon(self, h):
        self.h = h;
        self.N_lits = self.N_lits_t*self.h + self.N_rels;
        
        self.Total_Statement = copy.deepcopy(self.Init_Statement);
        self.Total_Statement.N_Vars = self.N_lits;
        
        for Clause in self.Goal_Statement.Clauses:
            New_Clause = [];
            for Lit in Clause:
                new_Lit = copy.copy(Lit);
                new_Lit.ID += self.N_lits_t*h;
                New_Clause.append(new_Lit);
            self.Total_Statement.Clauses.append(New_Clause);
        
        Action_Related_Clauses = self.Actions_Statement.Clauses + self.Frame_Statement.Clauses + self.Exclusive_Statement.Clauses;
        for t in range(h):
            for Clause in Action_Related_Clauses:
                New_Clause = [];
                for Lit in Clause:
                    new_Lit = copy.copy(Lit);
                    new_Lit.ID += self.N_lits_t*t;
                    New_Clause.append(new_Lit);
                self.Total_Statement.Clauses.append(New_Clause);
                
    #This method translates An_Atom which is a specific relation, and
    #converts it into a Literal at t=0.
    def Rel2Lit(self, An_Atom, arg_inds=None):
        if(len(An_Atom.Variables) != self.Relations[An_Atom.Name].Num_of_vars):
            raise(ValueError('Invalid Atom - Number of variables is incorrect'));
        
        Literal_ID = 0;
        for var in An_Atom.Variables:
            if(isinstance(var, str)):
                var_ind = [i for i in range(self.N_vars) if self.Variables[i]==var];
                if(len(var_ind) != 1):
                    raise(ValueError('Invalid Atom or Problematic Problem - Variables not found or found multiple times'));
                var_ind = var_ind[0];
            elif(isinstance(var, int)):
                var_ind = arg_inds[var];
            else:
                raise(ValueError('Invalid Atom - vars must be either str or int'));
            Literal_ID *= self.N_vars;
            Literal_ID += var_ind;
        
        #   Beggining of time bloc + offset to beggining of relation block
        Literal_ID += self.Relations[An_Atom.Name].Start_Ind;
        ret = Literal();
        ret.ID = Literal_ID;
        ret.Affirm = An_Atom.affirm;
        
        return ret;
    
    def decode_assignment(self, assignments):
        S = '';
        for t in range(self.h):
            
            Action_ID = [i for i in range(self.N_rels,self.N_rels+self.N_acts) if assignments[i+t*self.N_lits_t]];
            if(len(Action_ID) != 1):
                raise(ValueError('Incorrect number of active actions'));
            Action_ID = Action_ID[0];
            
            Action_name = [a for a in self.Actions if self.Actions[a].Ind==Action_ID];
            S += Action_name[0]+' ';
            
            for arg_ordinal in range(self.N_args):
                Arg_ID = [i for i in range(self.N_vars) if assignments[i+self.N_rels+self.N_acts+arg_ordinal*self.N_vars+t*self.N_lits_t]];
                
                if(len(Arg_ID) != 1):
                    raise(ValueError('Incorrect number of arguments'));
                
                S += self.Variables[Arg_ID[0]] + ' ';
            S += '\n';
        return S;
        
    def __repr__(self):
        S =  '\nVariables: %s\n'%self.Variables;
        S += 'Relations:';
        for rel in self.Relations:
            S += '\n  %s:\n%s'%(rel, self.Relations[rel]);
        S += '\nActions:';
        for act in self.Actions:
            S += '\n  %s:\n%s'%(act, self.Actions[act]);
        S+='\n';
        S+='Number of variables: %d\n'%self.N_vars;
        S+='Number of relations: %d\n'%self.N_rels;
        S+='Number of actions  : %d\n'%self.N_acts;
        S+='Number of arguments: %d\n'%self.N_args;
        S+='Numb of Lits per t : %d\n'%self.N_lits_t;
        S+='Initial State: %s\n'%self.InitialState;
        S+='Goal State   : %s\n'%self.GoalState;
        
        if(self.h != None):
            S+='Total number of literals for h=%d: %d\n'%(self.h, self.N_lits);
        
        S+='Pre-calculated values for encoding:\n';
        S+='\tInit_Statement: %s\n'%self.Init_Statement;
        S+='\tGoal_Statement: %s\n'%self.Goal_Statement;
        S+='\tActions_Statement: %s\n'%self.Actions_Statement;
        S+='\tFrame_Statement: %s\n'%self.Frame_Statement;
        S+='\tExclusive_Statement: %s\n'%self.Exclusive_Statement;
        
        return S;
        
    Init_Statement = SAT_Sentence();
    
    #The following sentences also have time_step set to 0. They'll have
    #to be offset to be put in the right timestep
    
    #This one must have t=h
    Goal_Statement = SAT_Sentence();
    
    #These ones must be repeated for t in range(h)
    Actions_Statement = SAT_Sentence();
    Frame_Statement = SAT_Sentence();
    Exclusive_Statement = SAT_Sentence();
    
    #The complete statement, for all time steps and everything.
    Total_Statement = SAT_Sentence();
    




