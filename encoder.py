#In this file is all the code related with encoding the PDLL problem into
#a SAT porblem. It is also capable of decoding an assignment into a human-
#readable string of action types and arguments

#In the code and comments, when we say "literals" we mean the literals 
#in a SAT sentence.
#When we say variables, we mean the variables in a PDLL problem, e.g. 
#for the blocks problems, they can be A,B,C,Table, etc.

#Actions are represented with overloaded splitting. This means some literals
#will represent the action type (e.g. move or move2Table) and others the
#ith argument taken by the action (e.g. arg1_A, arg1_B, arg2_B, etc...)

import re; #Regular expressions. Just to facilitate reading the file
#~ import pdb;
#~ from collections import OrderedDict; 
import copy;
from Quine_McCluskey_nary import *

from SAT_defs import *;



class Relation: #Information about a relation in the general sense
    def __init__(self):
        self.Num_of_vars = -1;
        self.Start_Ind = -1; #Literal index in which the literals associated with this relation start.
        
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
        
        self.Ind = -1; #Index of literal corresponding to this action type
        
        if(Variables != None):
            self.Vars = Variables;
            self.Num_of_args = len(Variables);
        
    #Add a new precondition or effect to this action
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
        self.Name = ''; #The relation or action type
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
    
    #new_args is a list of integers. For each i, new_args[i] denotes which
    #variable we will have as the self.Variables[i]'th variable.
    #Unfilled vars are left at -1. Incongruancies make this return false
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

#Contains all the information about a problem, including the SAT_sentence
#that expresses it, once the horizon is set.    
class problem:
    
    Factoring = True; #set to False to disable factoring - makes many problems take extremely long
    
    def __init__(self, fileHandle=None):
        
        #Initializing
        self.Variables = []; #List with the names of the variables
        
        
        self.Relations = dict();  #Dictionary with information about relation types, in the form of Relation objects
        self.Actions = dict(); #Dictionary with information about action types, in the form of Action objects
        
        #The following statements are defined at time_step 0, going to time_stem 1. Before used, some will have to be copied and time-shifted
        self.InitialState = []; #List of Atom objects corresponding to the initial state (not grounded)
        self.GoalState = []; #List of Atom objects corresponding to the goal state
        self.Init_Statement = SAT_Sentence(); #Statement referring to the initial state
        self.Goal_Statement = SAT_Sentence(); #Statement referring to the goal state
        self.Actions_Statement = SAT_Sentence(); #Statement with the A=>P,E axioms
        self.Frame_Statement = SAT_Sentence(); #Statement with the frame axioms
        self.Exclusive_Statement = SAT_Sentence(); #Statement cotaining the at-least-one and the at-most-one axioms, hereon sometimes referred the exactely-one-axioms
        
        self.Total_Statement = SAT_Sentence(); #Combination of the above statements, for all time_steps where they're relevant
        
        
            #Various useful counts:
        self.N_vars = 0; #Number of variables in PDLL problem
        self.N_rels = 0; #Number of relation types
        self.N_acts = 0; #Number of action types
        self.N_args = 0; #Maximum number of arguments of any action
        self.N_lits_t=0; #literals per time step (before horizon)
        self.N_lits = 0; #Total number of literals
        
        self.h = None; #Horizon
        
        if(fileHandle == None):
            return;
        
        self.read_from_file(fileHandle);
        
        self.prepare_literal_convertion();
        
        self.init_state_statements();
        
        if(self.Factoring):
            self.prepare_init_statements();
            self.init_action_statements();
        else:
            self.init_action_statements_no_factoring();
            
        
    
    #Extracts all the information from a file, putting it into a useful form for this class' functions to use
    def read_from_file(self, fileHandle):
        for line in fileHandle:
            #Setting the initial or goal states.
            if(line[0] == 'I' or line[0] == 'G'):
                
                for param in line.split()[1:]: 
                    this_relation = Atom(param);
                    
                    #Introduce newly found variables in self.Variables
                    for va in this_relation.Variables:
                        if(not va in self.Variables):
                            self.Variables.append(va);
                    
                    #Introduce newly found relation in self.Relations
                    Relation_info = self.Relations.setdefault(this_relation.Name, Relation());
                    
                    if(Relation_info.Num_of_vars != -1 and Relation_info.Num_of_vars != len(this_relation.Variables)):
                        raise(ValueError('Number of variables used by a relation shouldn\'t change')); 
                    Relation_info.Num_of_vars = len(this_relation.Variables);
                    
                    if(line[0] == 'I'):
                        this_relation.t = 0;
                        self.InitialState.append(this_relation);
                    elif(line[0] == 'G'):
                        self.GoalState.append(this_relation);
            #Defining an action    
            elif(line[0] == 'A'):
                #Getting action name and parameters to be used
                params = line.split();
                action_atom = Atom(params[1]);
                self.Actions[action_atom.Name] = Action(action_atom.Variables);
                this_action = self.Actions[action_atom.Name];
                
                #Recording action's preconditions and effects
                mode = 'Precond';
                for param in params[3:]:
                    if(param == '->'):
                        mode = 'Effects';
                        continue;
                    this_action.append(Atom(param), mode);
                
                #Inserting any newly found relations or variables (anything not in the action's variables is assumed to be a constant)
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
        
        #Relations get one literal for every possible combination of arguments for them
        for rel in self.Relations:
            self.Relations[rel].Start_Ind = self.N_rels;
            self.N_rels += self.N_vars**self.Relations[rel].Num_of_vars;
        
        #Actions get one literal for every different action type, plus self.Variables for every possible argument
        for act in self.Actions:
            self.N_args = max(self.N_args, self.Actions[act].Num_of_args);
            self.Actions[act].Ind = self.N_rels + self.N_acts;
            self.N_acts+=1;
        self.N_lits_t = self.N_rels+self.N_acts+self.N_args*self.N_vars;
    
    
    #Creating general information for what actions require or effect 
    #each relation in self.Relations, and how their arguments are related
    def prepare_init_statements(self):
        
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
                        rel.Precond.append(new_atom);
                        
                for effect in act.Effects:
                    if(effect.Name == rel_name):
                        new_atom = Atom();
                        new_atom.Name = act_name;
                        new_atom.Variables = effect.Variables;
                        new_atom.affirm = effect.affirm;
                        rel.Effects.append(new_atom);
        
    #Creating the SAT statements for initial and goal state
    def init_state_statements(self):
        #At init all possible lits are negated, except if they're 
        #present in self.InitialState. This makes the literals grounded
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
        
    
    #Precalculates action sentences, so they only need to be copied, time delayed, and joined together to make the actual problem statement:
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
                
                #Make a list of all the specific actions (in the form of atoms) that effect this rel
                acts_effects = [];
                for effect in rel.Effects:
                    new_atom = copy.copy(effect);
                    if(new_atom.replace_args(var_inds, self.Actions[new_atom.Name].Num_of_args, self.Variables )):
                        acts_effects.append(new_atom);
                
                #Create action implies precondition clauses
                for precond in acts_precond:
                    precond_lit = Literal( rel.Start_Ind + arg_comb_num, precond.affirm );
                    Base_Clause = self.Act2Clause(precond);
                    self.Actions_Statement.Clauses.append( Base_Clause + [precond_lit]);
                
                #actions_with_no_effect_per_act -> list indexed by true 
                #or false and by action type, corresponding to the argument 
                #combinations that make this rel become true or false, respectively
                
                #actions_with_no_effect -> list indexed by true or false, 
                #with the clauses corresponding to the actions that make 
                #this rel become true or false, respectively. Made by 
                #collapsing actions_with_no_effect_per_act with QM.join
                
                #At the beggining, actions_with_no_effect_per_act contains every single argument combination, for each action.
                actions_with_no_effect_per_act = [[],[]];
                for act_name in self.Actions:
                    act = self.Actions[act_name];
                    actions_with_no_effect_per_act[False].append( QM([self.N_vars]*act.Num_of_args) );
                    actions_with_no_effect_per_act[True].append( QM([self.N_vars]*act.Num_of_args) );
                
                
                #Create action implies effect clauses, and remove from actions_with_no_effect_per_act those argument combinations that do effect rel
                for effect in acts_effects:
                    effect_lit = Literal( rel.Start_Ind + arg_comb_num + self.N_lits_t, effect.affirm );
                    Base_Clause = self.Act2Clause(effect);
                    self.Actions_Statement.Clauses.append( Base_Clause + [effect_lit]);
                    
                    act_that_does_effect = [];
                    for arg in effect.Variables:
                        act_that_does_effect.append(arg);
                    
                    #Selecting the action type that does effect---VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
                    actions_with_no_effect_per_act[effect.affirm][Base_Clause[0].ID - self.N_rels].remove([act_that_does_effect]);
                    
                #initializing actions_with_no_effect empty
                actions_with_no_effect = [QM([self.N_acts] + [self.N_vars]*self.N_args, {}), QM([self.N_acts] + [self.N_vars]*self.N_args, {})];
                
                #Joining all actions together. Before joining, QM simplifies each group for efficiency
                for affirm_state in [False,True]:
                    actions_with_no_effect[affirm_state].join(actions_with_no_effect_per_act[affirm_state]);
                
                #Simplifying the clauses
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
        
        #Introducting the Initial state clauses
        self.Total_Statement = copy.deepcopy(self.Init_Statement);
        self.Total_Statement.N_Vars = self.N_lits;
        
        #Introducting the Goal state clauses, all shifted to the horizon
        for Clause in self.Goal_Statement.Clauses:
            New_Clause = [];
            for Lit in Clause:
                new_Lit = copy.copy(Lit);
                new_Lit.ID += self.N_lits_t*h;
                New_Clause.append(new_Lit);
            self.Total_Statement.Clauses.append(New_Clause);
        
        #Copying and shifting the time step for all time steps between 0 and h-1
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
    
    #This method translates An_Atom, wich can be in the form of a Atom
    #object, or a tuple (to work with QM), into a sequence of clauses
    #for the action type and each of the arguments
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
            
    #Receiving a list of boolean values associated with each literal,
    #this method produces a human-readable string with the actions that
    #were taken, following the output format defined by the teacher
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
    
    
    #Older code. Unused except in tests, when Factoring is set to False:
    
    def init_action_statements_no_factoring(self):
           
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
                Precond_Lits = [];
                for precond in act.Precond:
                    Precond_Lits.append(self.Rel2Lit(precond, var_inds));
                Precond_Lits = self.simplify(Precond_Lits);
                
                Effect_Lits = [];
                for effect in act.Effects:
                    Effect_Lit = self.Rel2Lit(effect, var_inds);
                    Effect_Lit.ID += self.N_lits_t; #Effects are on the next time step
                    Effect_Lits.append(Effect_Lit);
                Effect_Lits = self.simplify(Effect_Lits);
                
                if( (not Precond_Lits) or (not Effect_Lits) ):
                    self.Actions_Statement.Clauses.append(Base_Clause); #An indication that this action cannot be performed
                    continue; #No need to make the frame statements because of the above
                
                for Lit in (Precond_Lits+Effect_Lits):
                    This_Clause = Base_Clause + [Lit];
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
        At_Most_One_Clause = [];
        for k in range(self.N_args):
            At_Least_One_Clause = [Literal(self.N_rels+self.N_acts+k*self.N_vars+i,True) for i in range(self.N_vars)];
            At_Most_One_Clause = [];
            for i in range(self.N_vars):
                for j in range(i+1, self.N_vars):
                    At_Most_One_Clause.append( [Literal(self.N_rels+self.N_acts+k*self.N_vars+i,False), Literal(self.N_rels+self.N_acts+k*self.N_vars+j,False)] );
            self.Exclusive_Statement.Clauses += ([At_Least_One_Clause] + At_Most_One_Clause);         
    
    #Removes repeated literals, or everything in the list if 
    #contradicting literals are present.
    def simplify( self, lit_list ):
        lits_to_remove = [];
        
        for lit in lit_list:
            same_lits = [ l for l in lit_list if (l.ID == lit.ID) and (not l is lit) ];
            cont_lits = [ l for l in same_lits if l.Affirm != lit.Affirm ];
            
            if(cont_lits):
                lit_list = [];
                return lit_list;
                
            lits_to_remove += same_lits;
            
        for lit in lits_to_remove:
            lit_list.remove(lit);
        return lit_list;




