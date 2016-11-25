import sys;
import re;
import pprint;
import pdb;
from collections import OrderedDict; 

from SAT_defs import *;

class Relation: #Information about a relation in the general sense
    def __init__(self):
        self.Num_of_vars = -1;
        self.Start_Ind = -1; #Index of SAT_Variables in which the SAT_variables associated with this relation start.
    
    def __repr__(self):
        return '\tNum_of_Vars: %d\n\tStart_Ind: %d'%(self.Num_of_vars, self.Start_Ind);

class Action: #Information about an action in the general sense
    def __init__(self, Variables=None):
        self.Num_of_vars = 0;
        self.Vars = []; #Variables present in definition (used to convert variables to numbers)
        
        #Lists of atoms, with variables that are numbers going from 0 to Num_of_vars-1:
        self.Precond = [];
        self.Effects = [];
        
        self.Ind = -1;
        
        if(Variables != None):
            self.Vars = Variables;
            self.Num_of_vars = len(Variables);
        
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
        return '\tNum_of_Vars: %d\n\tPreconditions: %s\n\tEffects: %s\n\tInd: %d'%(self.Num_of_vars, self.Precond, self.Effects, self.Ind);
        
class Atom: #Represents a specific relation or action
    def __init__(self, string):
        self.Name = '';
        self.Variables = [];
        self.t = -1; #Time step
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
        if(self.t != -1):
            S+='_%d'%self.t;
        return S;
#Although there are issues with using this as an action if RAA encoding is to be used...
    
class problem:
    
    def __init__(self, fileHandle=None):
        self.Variables = [];
        #The order in a dict varies. Using OrderedDict instead:
        self.Relations = OrderedDict(); 
        self.Actions = OrderedDict();
        
        #States in the form of lists of atoms
        self.InitialState = []; 
        self.GoalState = [];
        
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
        self.N_rels = 0;
        for rel in self.Relations:
            self.Relations[rel].Start_Ind = self.N_rels;
            self.N_rels += self.N_vars**self.Relations[rel].Num_of_vars;
        self.N_acts = 0;
        self.N_args = 0;
        for act in self.Actions:
            self.N_args = max(self.N_args, self.Actions[act].Num_of_vars);
            self.Actions[act].Ind = self.N_rels + self.N_acts;
            self.N_acts+=1;
    
    def set_horizon(self, h):
        self.h = h;
        for rel in self.GoalState:
            rel.t = h;
            
    #This method translates An_Atom which is a specific relation, and
    #converts it into the number of variable it is.
    def Rel2LitInd(self, An_Atom):
        if(len(An_Atom.Variables) != self.Relations[An_Atom.Name].Num_of_vars):
            raise(ValueError('Invalid Atom - Number of variables is incorrect'));
        
        Literal_ID = 0;
        for var in An_Atom.Variables:
            var_ind = [i for i in range(self.N_vars) if self.Variables[i]==var];
            if(len(var_ind) != 1):
                raise(ValueError('Invalid Atom or Problematic Problem - Variables not found or found multiple times'));
            Literal_ID *= self.N_vars;
            Literal_ID += var_ind[0];
        
        #   Beggining of time bloc + offset to beggining of relation block
        Literal_ID += (self.N_rels+self.N_acts+self.N_args*self.N_vars)*An_Atom.t + self.Relations[An_Atom.Name].Start_Ind;
        return Literal_ID;
   
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
        S+='Initial State: %s\n'%self.InitialState;
        S+='Goal State   : %s\n'%self.GoalState;
        
        if(self.h>=0):
            S+='Total number of literals for h=%d: %d\n'%(self.h, self.N_rels*(self.h+1)+(self.N_acts+self.N_args*self.N_vars)*self.h);
        return S;


fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(3);
pprint.pprint(ThisProblem);


