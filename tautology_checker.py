"""
Implementation of RS method to verify if the provided propositional logic is a Tautology.
Group Members: Vinit Shah, Satwik Rao, Koosha Sharifani, Xiangcheng Wu 
"""

import sys


class Expression:
    """ Class to evaluate the propositional logic whether it is a tautology """

    def __and__(self, other):
        """ Overwrites the inbuilt and function """
        return ConjunctionOperator(self, other)

    def __or__(self, other):
        """ Overwrites the inbuilt or function """
        return DisjunctionOperator(self, other)

    def __rshift__(self, other):
        """ Overwrites the inbuilt rshift function """
        return ImplicationOperator(self, other)

    def __lshift__(self, other):
        """ Overwrites the inbuilt lshift function """
        return BiconditionalOperator(self, other)

    def __invert__(self):
        """ Overwrites the inbuilt invert function """
        return NegationOperator(self)

    def __eq__(self, other):
        """ Overwrites the inbuilt eq function """
        return self.__class__ == other.__class__ and self.equals(other)

    def _update_leaves(self, left_side, right_side):
        """ Updates the leaves of the tree and also updates the fundamental list 
            if the expression is found to be fundamental 
        """
        leaves = [f"~{node}" for node in left_side]
        leaves.extend([str(node) for node in right_side])
        leaf_list.append(leaves)
        global is_fundamental
        if len(left_side) == len(right_side):
            count = 0
            for node in left_side:
                if node in right_side:
                    count += 1
            if len(left_side) == count:
                is_fundamental = False
                fundamental_list.append(leaves)
        if is_fundamental:
            fundamental_list.append(leaves)

    def _evaluate_left(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        is_nf = True
        is_return = None
        for expression in left_side:
            if expression in right_side:
                self._update_leaves(left_side, right_side)
                is_return = True
            if not isinstance(expression, Proposition):
                left_side.remove(expression)
                left_prop = expression._left_side(left_side, right_side)
                left_side, right_side = left_prop[0]
                if len(left_prop) > 1:
                    res = self.evaluate(*left_prop[1])
                    if not res:
                        is_return = False
                is_nf = False
                break
        return left_side, right_side, is_nf, is_return

    def _evaluate_right(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        is_nf = True
        is_return = None
        for expression in right_side:
            if expression in left_side:
                self._update_leaves(left_side, right_side)
                is_return = True
            if not isinstance(expression, Proposition):
                right_side.remove(expression)
                right_prop = expression._right_side(left_side, right_side)
                left_side, right_side = right_prop[0]
                if len(right_prop) > 1:
                    res = self.evaluate(*right_prop[1])
                    if not res:
                        is_return = False
                is_nf = False
                break
        return left_side, right_side, is_nf, is_return

    def evaluate(self, left_side, right_side):
        """ Evaluates the left and right side based on the RS method """
        try:
            while True:
                is_nf = True
                left_side, right_side, is_nf, is_return = \
                    self._evaluate_left(left_side, right_side)
                if is_return is not None:
                    return is_return
                left_side, right_side, is_nf, is_return = \
                    self._evaluate_right(left_side, right_side)
                if is_return is not None:
                    return is_return
                if is_nf:
                    return False
        except Exception as e:
            print(f"Exception caught while evaluating the expression {e}")


class Proposition(Expression):
    """ Generic class for generating the propositonal variables """

    def __init__(self, name):
        """ Initializes the variable name """
        self.name = name

    def __str__(self):
        """ Represents the class object into the string """
        return str(self.name)

    def equals(self, other):
        """ Checks whether the left and right child of other object is equal to current object """
        return self.name == other.name


class ConjunctionOperator(Expression):
    """ Class to perform AND operation for the inputs """

    def __init__(self, left_child, right_child):
        """ Initializes the left and right child """
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        return (left_side + [self.left_child, self.right_child], right_side),

    def _right_side(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        return (left_side, right_side + [self.left_child]), \
            (left_side, right_side + [self.right_child])

    def __str__(self):
        """ Represents the class object into the string """
        return f"({self.left_child} ^ {self.right_child})"

    def equals(self, other):
        """ Checks whether the left and right child of other object is equal to current object """
        return self.left_child == other.left_child and self.right_child == other.right_child


class DisjunctionOperator(Expression):
    """ Class to perform OR operation for the inputs """

    def __init__(self, left_child, right_child):
        """ Initializes the left and right child """
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        return (left_side + [self.left_child], right_side), \
            (left_side + [self.right_child], right_side)

    def _right_side(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        return (left_side, right_side + [self.left_child, self.right_child]),

    def __str__(self):
        """ Represents the class object into the string """
        return f"({self.left_child} v {self.right_child})"

    def equals(self, other):
        """ Checks whether the left and right child of other object is equal to current object """
        return self.left_child == other.left_child and self.right_child == other.right_child


class ImplicationOperator(Expression):
    """ Class to perform implication operation for the inputs """

    def __init__(self, left_child, right_child):
        """ Initializes the left and right child """
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        return (left_side + [self.right_child], right_side), \
            (left_side, right_side + [self.left_child])

    def _right_side(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        return (left_side + [self.left_child], right_side + [self.right_child]),

    def __str__(self):
        """ Represents the class object into the string """
        return f"({self.left_child} => {self.right_child})"

    def equals(self, other):
        """ Checks whether the left and right child of other object is equal to current object """
        return self.left_child == other.left_child and self.right_child == other.right_child


class BiconditionalOperator(Expression):
    """ Class to perform biconditional operation for the inputs """

    def __init__(self, left_child, right_child):
        """ Initializes the left and right child """
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        return (left_side + [self.left_child, self.right_child], right_side), \
            (left_side, right_side + [self.left_child, self.right_child])

    def _right_side(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        return (left_side + [self.left_child], right_side + [self.right_child]), \
            (left_side + [self.right_child], right_side + [self.left_child])

    def __str__(self):
        """ Represents the class object into the string """
        return f"({self.left_child} <=> {self.right_child})"

    def equals(self, other):
        """ Checks whether the left and right child of other object is equal to current object """
        return self.left_child == other.left_child and self.right_child == other.right_child


class NegationOperator(Expression):
    """ Class to perform Negation operation for the inputs """

    def __init__(self, child):
        """ Initializes the expression """
        self.child = child

    def _left_side(self, left_side, right_side):
        """ Evaluates the left side of the tree """
        return (left_side, right_side + [self.child]),

    def _right_side(self, left_side, right_side):
        """ Evaluates the right side of the tree """
        return (left_side + [self.child], right_side),

    def __str__(self):
        """ Represents the class object into the string """
        return f"~{self.child}"


def initialize_variables(*prop):
    """ Initializes propositional variables """
    return (Proposition(name) for name in prop)


if __name__ == '__main__':
    """ 
    INPUT: Enter the propositional formula to check if it is a tautology.
    OUTPUT: Prints whether the formula is a tautology or not. 
            If formula is a tautology, then it prints the leaves and fundamental nodes.
    The variables => a, b, c, d can be used for developing the formula.
    Below are the operators which can be used for generating the formula:
        Negation Operator      ~
        Conjunction Operator   &
        Disjunction Operator   |
        Implication Operator   >>
        Biconditional Operator <<
    Below are the examples of formula:
        ~(a >> c) >> (~(c | d) >> (a & ~c))
        ~(a >> c) >> (~(c | d) >> (a & c))
    """
    # List to hold the leaf nodes
    leaf_list = []
    # List to hold the fundamental nodes
    fundamental_list = []
    # Variable to check if the fundamental node is found
    is_fundamental = True
    # Initializes the variables for the formula
    a, b, c, d = initialize_variables('a', 'b', 'c', 'd')
    expression = input("Enter the Formula: ")
    try:
        prop_expr = eval(expression.lower())
    except Exception as e:
        print(f"Error occured while evaluating the expression: {e}")
        print(f"Please use the variables: a, b, c, d for the formula")
        sys.exit(1)
    # Calls the evaluate function to determine whether the formula is a tautology
    is_tautology = prop_expr.evaluate([], [prop_expr])
    if is_tautology:
        print(f"Propotional Formula {prop_expr} is a Tautology")
        print(f"Leaves of the tree: {leaf_list}")
        print(f"Fundamental nodes: {fundamental_list}")
        sys.exit(0)
    else:
        print(f"Propotional Formula {prop_expr} is NOT a Tautology")
        sys.exit(1)
