#Inspired by the Quine McCluskey algorithm, as implemented in 
#http://stackoverflow.com/a/11454049/1577940, but generalized to work
#n-ary variables, instead of just binary (or boolean) ones. Very little,
#if any, of his original code remains.

#From hereon, in the code and comments, the "arity" of a variable is the
#number of possible values it may have, besides -1, which stands for an
#"any", or in other words, a variable that could be any option and still
#make a true clause. In a SAT representation of a clause, the "anys" would
#be ommited

import copy;
import pprint;

class QM:
    
    #Initialize QM object. If Clauses are absent, it creates all possible
    #clauses for these variables.
    def __init__(self, Arities, Clauses=None):
        self.Arities = Arities; #Defines the arities of each variable
        self.Clauses = set(); #set of tuples of ints. -1 represents "any"
        
        if(Clauses == None):
            #Making all possible clauses
            self.Clauses.add( tuple( [-1]*len(Arities) ) );
            self.expand(); 
        else:
            for Clause in Clauses:
                
                Clause = list(Clause);
                
                if(len(Clause) > len(Arities)):
                    raise(ValueError('Too many elements in a clause'));
                
                #Extending the clauses until they have the valid length
                for i in range(len(Clause), len(Arities)):
                    raise(ValueError);
                    Clause.append(-1);
                Clause = tuple(Clause);
                    
                self.Clauses.add(Clause);
    
    #Expands all clauses, removing all clauses with "any"s, and inserting
    #clauses with those any's filled with all possible combinations of
    #values
    def expand(self):
        
        new_Clauses = set();
        
        for Clause in self.Clauses:
            anys = [i for i in range(len(Clause)) if Clause[i]==-1];
            
            if(not anys):
                new_Clauses.add(Clause);
                continue;
            
            anys_assign = [0]*len(anys);
            
            while(True):
                
                #Making a clause
                new_Clause = list(Clause);
                for i in range(len(anys)):
                    new_Clause[anys[i]] = anys_assign[i];
                new_Clauses.add(tuple(new_Clause));
                
                #Incrementing anys_assign
                for i in range(len(anys)):
                    anys_assign[i] += 1;
                    if(anys_assign[i] == self.Arities[anys[i]]):
                        anys_assign[i] = 0;
                    else:
                        break;
                if(i==len(anys)-1 and anys_assign[i]==0):
                    break;
                    
        self.Clauses = new_Clauses;
    
    #Removes Clauses. self must have no clauses with "anys".
    def remove(self, Clauses): #Clauses must be a list of tuples
        aux = QM(self.Arities, Clauses);
        aux.expand();
        self.Clauses.difference_update(aux.Clauses);
    
    #Joins a series of QM objects. The first variable represents from
    #which QM object a clause came from
    def join(self, QM_list):
        j = 0;
        for QM_object in QM_list:
            
            QM_object.simplify();
            
            for Clause in QM_object.Clauses:
                
                Clause = [j] + list(Clause);
                
                if(len(Clause) > len(self.Arities)):
                    raise(ValueError('Too many elements in a clause'));
                
                #Extending the clauses until they have the valid length
                for i in range(len(Clause), len(self.Arities)):
                    Clause.append(-1);
                Clause = tuple(Clause);
                    
                self.Clauses.add(Clause);
                
            j+=1;
        
        
    #~ def add(self, Clauses): #Clauses must be a list of tuples
        #~ aux = QM(self.Arities, Clauses);
        #~ aux.expand();
        #~ self.Clauses.update(aux.Clauses);
    
    #Compares 2 clauses, returning the index of an element if it's the 
    #only one different between the two, or None if more than 1 variable 
    #is different. If they're the same, returns error, as this is not 
    #expected to happen ever
    def compare(self, Clause1, Clause2):
        diffs = [];
        N = 0;
        for i in range(len(self.Arities)):
            if(Clause1[i] != Clause2[i]):
                if(N>=1):
                    return None;
                diffs.append(i);
                N+=1;
                
        if(N == 0):
            raise(ValueError('Two equal clauses!?!?!?!'));
        elif(N == 1):
            return diffs[0];
        else:
            return None;
                
        
    def simplify(self):
        
        Clauses_by_grouping = [set() for i in range(len(self.Arities)+1)]; #List of sets
        
        for Clause in self.Clauses:
            Clause_grouping = len([i for i in Clause if i==-1]);
            Clauses_by_grouping[Clause_grouping].add(Clause);
        
        self.Clauses = set();
        
        grouping = 0;
        
        while( Clauses_by_grouping[grouping] and grouping <  len(self.Arities) ):
            
            #~ Clauses_by_grouping.append(set());
            Clauses_temp = list(Clauses_by_grouping[grouping]); #The one we're working on
            N_clauses = len(Clauses_temp);
            
            for i in range(N_clauses-1):
                Similars = [ [] for i in range(len(self.Arities))];
                
                #Producing a list of indices of clauses which are similar (only differ in one element) to Clauses_temp[i]
                for j in range(i+1, N_clauses):
                    d_ind = self.compare(Clauses_temp[i],Clauses_temp[j]);
                    if(d_ind != None):
                        Similars[d_ind].append(j);
                
                
                #All those that cover a whole index will be collapsed into one.
                for j in range(len(self.Arities)):
                    if(len(Similars[j]) == self.Arities[j]-1 and self.Arities[j]!=1): #Unary variables can lead to repeatedly combining one variable, making this program never end
                        
                        Clauses_by_grouping[grouping].difference_update( [ Clauses_temp[n] for n in (Similars[j]+[i]) ] );
                        
                        To_Add = list(Clauses_temp[i]);
                        To_Add[j] = -1;
                        Clauses_by_grouping[grouping+1].add(tuple(To_Add));
            grouping += 1;
        
        for cause_group in Clauses_by_grouping:
            self.Clauses.update(cause_group);
        
