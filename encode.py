import sys;
import re;
import pdb;
from collections import OrderedDict; 
import copy;
from Quine_McCluskey_nary import *

from SAT_defs import *;

class Relation: #Information about a relation in the general sense
    def __init__(self):
        self.Num_of_vars = -1;
        self.Start_Ind = -1; #Index of SAT_Variables in which the SAT_variables associated with this relation start.
        
        self.Precond = []; #List of atoms (with ints args) that correspond to actions that would require this relation as a precondition
        self.Effects = []; #List of atoms (with ints args) that correspond to actions that would produce this relation as an effect
        
    def __repr__(self):
        return '\tNum_of_Vars: %d\n\tStart_Ind: %d\n\tPreconditions:%s\n\tEffects:%s'%(self.Num_of_vars, self.Start_Ind, self.Precond, self.Effects);

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
            varind = [j for j in range(len(self.Vars)) if self.Vars[j]==var];
            
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
    def __init__(self, string=''):
        self.Name = '';
        self.Variables = []; #Strings for actual variable names, ints for when they are to index some list
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
    
    #new_args defines what variables we will have for the arguments at the positions indicated by self.Variables. Irrelevants are left at -1. Incongruancies make this return false
    def replace_args(self, new_args, N_Args, Variable_Names):
        new_Variables = [-1]*N_Args;
        
        for i in range(len(self.Variables)):
            var = self.Variables[i];
            if(isinstance(var, int)):
                if(new_Variables[var]!=-1 and new_Variables[var]!=new_args[i]):
                    return False;
                
                new_Variables[var] = new_args[i];
            else:
                if(var != Variable_Names[new_args[i]]):
                    return False;
        
        self.Variables = new_Variables;
        return True;
    
    def __repr__(self):
        
        if(self.affirm):
            S = '';
        else:
            S = '-';
        S += '%s%s'%(self.Name, self.Variables);
        return S;
    
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
        
        #Initializing
        self.Variables = [];
        self.Relations = OrderedDict(); 
        self.Actions = OrderedDict();
        self.InitialState = []; 
        self.GoalState = [];
        self.Init_Statement = SAT_Sentence();
        self.Goal_Statement = SAT_Sentence();
        self.Actions_Statement = SAT_Sentence();
        self.Frame_Statement = SAT_Sentence();
        self.Exclusive_Statement = SAT_Sentence();
        self.Total_Statement = SAT_Sentence();
        
        if(fileHandle == None):
            return;
        
        self.read_from_file(fileHandle);
        
        self.prepare_literal_convertion();
        
        self.prepare_init_statements();
        
        self.init_state_statements();
        self.init_action_statements();
    
    #Extracts all the information from a file, putting it into a useful form for this class' functions to use
    def read_from_file(self, fileHandle):
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
    
    #Selects the region in the literal space where each variable will be
    def prepare_literal_convertion(self):
        self.N_vars = len(self.Variables);
        for rel in self.Relations:
            self.Relations[rel].Start_Ind = self.N_rels;
            self.N_rels += self.N_vars**self.Relations[rel].Num_of_vars;
        
        for act in self.Actions:
            self.N_args = max(self.N_args, self.Actions[act].Num_of_args);
            self.Actions[act].Ind = self.N_rels + self.N_acts;
            self.N_acts+=1;
        self.N_lits_t = self.N_rels+self.N_acts+self.N_args*self.N_vars;
    
    def prepare_init_statements(self):
        
        #Creating general information for what actions require or effect the relation
        for rel_name in self.Relations:
            rel = self.Relations[rel_name];
            
            for act_name in self.Actions:
                act = self.Actions[act_name];
                
                for precond in act.Precond:
                    if(precond.Name == rel_name):
                        new_atom = Atom();
                        new_atom.Name = act_name;
                        new_atom.Variables = precond.Variables;
                        new_atom.affirm = precond.affirm;
                        #~ new_atom = copy.deepcopy(precond);
                        #~ new_atom.Name = act_name;
                        rel.Precond.append(new_atom);
                        
                for effect in act.Effects:
                    if(effect.Name == rel_name):
                        new_atom = Atom();
                        new_atom.Name = act_name;
                        new_atom.Variables = effect.Variables;
                        new_atom.affirm = effect.affirm;
                        #~ new_atom = copy.deepcopy(effect);
                        #~ new_atom.Name = act_name;
                        rel.Effects.append(new_atom);
        
    def init_state_statements(self):
        #At init all possible lits are negated, except if they're 
        #present in self.InitialState
        Lits = [Literal(i, False) for i in list(range(self.N_rels))];
        for atom in self.InitialState:
            lit = self.Rel2Lit(atom);
            Lits[lit.ID] = lit;
        #Putting in clause form
        self.Init_Statement.Clauses = [[lit] for lit in Lits];
        
        self.Goal_Statement.Clauses = [];
        #Clauses for Goal state
        for atom in self.GoalState:
            lit = self.Rel2Lit(atom);
            self.Goal_Statement.Clauses.append([lit]);
        
    
    #Precalculates sentences, so they only need to be copied, time delayed, and joined together to make the actual problem statement:
    def init_action_statements(self):
        
        #For every specific relation
        for rel_name in self.Relations:
            rel = self.Relations[rel_name];
            #~ pdb.set_trace();
            #Combination of arguments seen as a number of base self.N_vars
            for arg_comb_num in range(self.N_vars**rel.Num_of_vars):
                
                rel_ID = rel.Start_Ind + arg_comb_num;
                
                #Obtaining the argument combination in list form
                aux_arg_comb_num = arg_comb_num;
                var_inds = [];
                for arg_ordinal in range(rel.Num_of_vars): #Translating arg_comb_num into a list of variable indexes
                    var_inds.append(aux_arg_comb_num%self.N_vars);
                    aux_arg_comb_num//=self.N_vars;
                var_inds.reverse();
                
                #Make a list of all the specific actions (in the form of atoms) that require this rel
                acts_precond = [];
                for precond in rel.Precond:
                    new_atom = copy.copy(precond);
                    if(new_atom.replace_args(var_inds, self.Actions[new_atom.Name].Num_of_args, self.Variables)):
                        acts_precond.append(new_atom);
                #Remove redundancies, or forbid the action if impossible. TODO
                
                #Make a list of all the specific actions (in the form of atoms) that effect this rel
                acts_effects = [];
                for effect in rel.Effects:
                    new_atom = copy.copy(effect);
                    if(new_atom.replace_args(var_inds, self.Actions[new_atom.Name].Num_of_args, self.Variables )):
                        acts_effects.append(new_atom);
                #Remove redundancies, or forbid the action if impossible. TODO
                
                #~ pdb.set_trace();
                
                #Create action implies precondition clauses
                for precond in acts_precond:
                    precond_lit = Literal( rel.Start_Ind + arg_comb_num, precond.affirm );
                    Base_Clause = self.Act2Clause(precond);
                    self.Actions_Statement.Clauses.append( Base_Clause + [precond_lit]);
                
                #At the beggining, actions_with_no_effect contains every single action, for a change to false or to true
                actions_with_no_effect = [QM([self.N_acts] + [self.N_vars]*self.N_args), QM([self.N_acts] + [self.N_vars]*self.N_args)]; #Can't use *2 as that would make them both the same
                
                #Create action implies effect clauses, and remove from actions_with_no_effect those actions that do have an effect
                for effect in acts_effects:
                    effect_lit = Literal( rel.Start_Ind + arg_comb_num + self.N_lits_t, effect.affirm );
                    Base_Clause = self.Act2Clause(effect);
                    self.Actions_Statement.Clauses.append( Base_Clause + [effect_lit]);
                    
                    act_that_does_effect = [Base_Clause[0].ID - self.N_rels];
                    for arg in effect.Variables:
                        act_that_does_effect.append(arg);
                    
                    actions_with_no_effect[effect.affirm].remove([act_that_does_effect]);
                
                for affirm_state in [False,True]:
                    actions_with_no_effect[affirm_state].simplify();
                
                #Converting actions_with_no_effect to SAT_Sentence
                for affirm_state in [False,True]:
                    for action in actions_with_no_effect[affirm_state].Clauses:
                        Base_Clause = self.Act2Clause(action);
                        Literal_Now = Literal(rel_ID, not affirm_state);
                        Literal_After = copy.copy(Literal_Now);
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
        At_Most_One_Clause = [];
        for k in range(self.N_args):
            At_Least_One_Clause = [Literal(self.N_rels+self.N_acts+k*self.N_vars+i,True) for i in range(self.N_vars)];
            At_Most_One_Clause = [];
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
    
    def Act2Clause(self, An_Atom):
        
        if(isinstance(An_Atom, Atom)):
            Clause = [Literal(self.Actions[An_Atom.Name].Ind, False)];
            
            for n_arg in range(len(An_Atom.Variables)) :
                
                var = An_Atom.Variables[n_arg];
                
                assert(isinstance(var,int));
                if(var != -1):
                    Clause.append(Literal( self.N_rels + self.N_acts + self.N_vars*n_arg + var, False ));
        elif(isinstance(An_Atom, tuple)):
            An_Atom = list(An_Atom);
            
            if(An_Atom[0] == -1):
                Clause = [];
            else:
                Clause = [Literal(An_Atom[0]+self.N_rels, False)];
            
            i = 0;
            for arg in An_Atom[1:]:
                if(arg!=-1):
                    Clause.append(Literal(arg + self.N_vars*i + self.N_rels + self.N_acts, False));
                    
                i+=1;
        
        return Clause;
            
    
    def decode_assignment(self, assignments):
        S = '';
        
        for t in range(self.h):
            
            Action_ID = [i for i in range(self.N_rels,self.N_rels+self.N_acts) if assignments[i+t*self.N_lits_t]];
            if(len(Action_ID) != 1):
                raise(ValueError('Incorrect number of active actions'));
            Action_ID = Action_ID[0];
            
            Action_name = [a for a in self.Actions if self.Actions[a].Ind==Action_ID];
            Action_name = Action_name[0];
            S += Action_name+' ';
            
            for arg_ordinal in range(self.Actions[Action_name].Num_of_args):
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
    




