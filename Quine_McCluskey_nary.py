#Inspired by the Quine McCluskey algorithm, as implemented in 
#http://stackoverflow.com/a/11454049/1577940, but generalized to work
#n-ary variables, instead of just binary (or boolean) ones.

import copy;
import pdb;
import pprint;

class QM:
    
    def __init__(self, Arities, Clauses=None):
        self.Arities = Arities; #Defines the arities of each variable
        self.Clauses = set(); #set of tuples of ints. -1 represents "any"
        
        if(Clauses == None):
            #Making all possible clauses
            self.Clauses.add( tuple( [-1]*len(Arities) ) );
            self.expand(); 
        else:
            for Clause in Clauses:
                if(len(Clause) > len(Arities)):
                    raise(ValueError('Too many elements in a clause'));
                
                #Extending the clauses until they have the valid length
                for i in range(len(Clause), len(Arities)):
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
    
    def remove(self, Clauses): #Clauses must be a list of tuples
        aux = QM(self.Arities, Clauses);
        aux.expand();
        self.Clauses.difference_update(aux.Clauses);
        
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
        
        Clauses_by_grouping = [self.Clauses]; #List of sets
        
        while( Clauses_by_grouping[-1] ):
            
            Clauses_by_grouping.append(set());
            Clauses_temp = list(Clauses_by_grouping[-2]); #The one we're working on
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
                        
                        Clauses_by_grouping[-2].difference_update( [ Clauses_temp[n] for n in (Similars[j]+[i]) ] );
                        
                        To_Add = list(Clauses_temp[i]);
                        To_Add[j] = -1;
                        Clauses_by_grouping[-1].add(tuple(To_Add));
                
        for cause_group in Clauses_by_grouping[1:]:
            self.Clauses.update(cause_group);
        

#~ a = QM([2,4,4,4]);
#~ a.Clauses.add( (1,2) );
#~ a.Clauses.add( (1,2) );
#~ a.Clauses.add( (-1,1) );
#~ a.Clauses.add( (-1,-1) );

#~ a.expand();
#~ a.remove( [[0]] );
#~ a.Clauses.add( (0,0,0,0) );
#~ a.simplify();
#~ pprint.pprint((a.Clauses));
