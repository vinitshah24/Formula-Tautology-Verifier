# This program is to check if the given Propositional Formula is a tautology or not 
# And to  display the fundamental leaves until the non-fundamental leaf is encountered in the tree implementation 
# using resolution steps of RS (Rasiowa and Sikorski) method if the propositional formula is a tautology.

# Program Input:
# Propositional formula with following symbols and variables enclosed in quotes (‘’) based on python version.
# Enter the input in variables of either a,b,c,d,p,q,r,s
# Foroperation 'and' use &
# For operation 'or' use |
# For operation '->' use >>
# For operation 'not' use ~

# Program Output:
# Output shows if the Expression is/ is not a tautology
# and displays the fundamental leaves until the non fundamental leaves are encountered while parsing if the propositional formula is a tautology.


# creating global variables
global leafnodes;
global fundamentals;
global nonfundamentalnodefound;

# Class to perform functions like not, and , or, right shift, left shift, equal , append leaves, is fundamental and call function 
class LogicalExpression:
    #overriding inbuilt invert method of python
    def __invert__(self):
        return Not(self)

    #overriding inbuilt and method of python
    def __and__(self, other):
        return And(self, other)

    #overriding inbuilt or method of python
    def __or__(self, other):
        return Or(self, other)

    #overriding inbuilt rshift method of python
    def __rshift__(self, other):
        return Implies(self, other)

    #overriding inbuilt lshift method of python
    def __lshift__(self, other):
        return Iff(self, other)

    #overriding inbuilt equals method of python
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.eq(other)
    
    # Here we append all the leafnodes to leafnodes global variable and fundamental nodes to fundamentals global variable.
    def _appendleafnodes(self, left, right):
        temp = ["~"+str(x) for x in left]
        temp += [str(x) for x in right]
        leafnodes.append(temp)
        if(self._isfundamental(left, right)):
            fundamentals.append(temp)
    
    # private method that returns if given left and right array composed of fundamental-node or not.
    def _isfundamental(self, left, right):
        global nonfundamentalnodefound
        
        # If the length of negated nodes count equals to nodes count and if the nodes between them are same, it's non-fundamental node
        if((len(left) == len(right))):
            count = 0
            for x in left:
                if x in right:
                    count += 1
            if(len(left) == count):
                nonfundamentalnodefound = True
                return False
        # If we already met non-fundamental node then all the leaf nodes following it are non-fundamental.
        return (True and nonfundamentalnodefound==False)

    # A function to determine if the expression is tautology or not.
    def call_func(self, left, right):

        while True:
            found = True
            for item in left:
                if item in right:
                    self._appendleafnodes(left, right)
                    return None
                if not isinstance(item, Variable):
                    left.remove(item)
                    temp_list = item._tleft(left, right)
                    left, right = temp_list[0]
                    if len(temp_list) > 1:
                        new_tuple = self.call_func(*temp_list[1])
                        if new_tuple is not None:
                            return new_tuple
                    found = False
                    break
            for item in right:
                if item in left:    
                    self._appendleafnodes(left, right)
                    return None
                if not isinstance(item, Variable):
                    right.remove(item)
                    temp_list = item._tright(left, right)
                    left, right = temp_list[0]
                    if len(temp_list) > 1:
                        new_tuple = self.call_func(*temp_list[1])
                        if new_tuple is not None:
                            return new_tuple
                    found = False
                    break
            if found:
                return "Expression is not a tautology"

    def _call_func(self):
        return self.call_func([], [self])

# Class to handle binary operations, and, or, implies, negation
class Bin_Op(LogicalExpression):
    def __init__(self, left_child, right_child):
        self.left_child = left_child
        self.right_child = right_child

    def __str__(self):
        return '(' + str(self.left_child) + ' ' + self.op + ' ' + str(self.right_child) + ')'

    def eq(self, other):
        return self.left_child == other.left_child and self.right_child == other.right_child

# class to carry out 'and' operation
class And(Bin_Op):
    op = '^'

    def _tleft(self, left, right):
        return (left + [self.left_child, self.right_child], right),

    def _tright(self, left, right):
        return (left, right + [self.left_child]), (left, right + [self.right_child])

# class to carry out 'implies/implication" operation
class Implies(Bin_Op):
    op = '->'

    def _tleft(self, left, right):
        return (left + [self.right_child], right), (left, right + [self.left_child])

    def _tright(self, left, right):
        return (left + [self.left_child], right + [self.right_child]),

# class to carry out 'not/negation' operation
class Not(LogicalExpression):
    def __init__(self, child):
        self.child = child

    def __str__(self):
        return '~' + str(self.child)

    def eq(self, other):
        return self.child == other.child

    def _tleft(self, left, right):
        return (left, right + [self.child]),

    def _tright(self, left, right):
        return (left + [self.child], right),

# class to carry out 'or' operation
class Or(Bin_Op):
    op = 'V'

    def _tleft(self, left, right):
        return (left + [self.left_child], right), (left + [self.right_child], right)

    def _tright(self, left, right):
        return (left, right + [self.left_child, self.right_child]),

# To create operands.
class Variable(LogicalExpression):
    def __init__(self, name):
        self.name = name

    def __hash__(self):
        return hash(self.name)

#To convert the operands entered into string
    def __str__(self):
        return str(self.name)

    __repr__ = __str__

    def eq(self, other):
        return self.name == other.name


a = Variable('a')
b = Variable('b')
c = Variable('c')
d = Variable('d')
p = Variable('p')
q = Variable('q')
r = Variable('r')
s = Variable('s')

# array that contains all the fundamental leaf-nodes
fundamentals = []
# flag to be set when first non-fundamental node found
nonfundamentalnodefound = False
# leaf nodes array contains all the leaf nodes
leafnodes = []


def rs_function(e):
    print("Formula entered: ", e)
    result = e._call_func()
    if result == None:
        print("All Leaf Nodes:", leafnodes)
        print("Fundamental Nodes:", fundamentals)
        
        print("Result: Expression is a Tautology")
    else:
        print("Result: Expression is not a Tautology")

inputString = input("Please enter a Propositional Formula:")

try:
    inputString = inputString.lower()
#     inputString = "(a>>b)>>((b>>c)>>(a>>c))"
#     inputString = "(a>>(a|b))"
#     inputString = "(~(a>>c)>>(~(c|d)>>(a&~c)))"
#     inputString = "(~(a>>c)>>(~(c|d)>>(a&c)))"
    e = eval(inputString)
    rs_function(e)
except NameError as e:
    # Input the propositional formula
    print("Please enter a valid Propositional Formula!!!", e)