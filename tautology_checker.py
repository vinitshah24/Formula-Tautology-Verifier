"""
Implementation of RS method to verify if the provided propositional logic is a Tautology.
"""


class Expression:
    """ Class to evaluate the propositional logic whether it is a tautology """

    def __invert__(self):
        """ Overwrites the inbuilt invert function """
        return NegationOperator(self)

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

    def __eq__(self, other):
        """ Overwrites the inbuilt eq function """
        return self.__class__ == other.__class__ and self.equals(other)

    # def _is_fundamental(self, left_side, right_side):
    #     return is_fundamental

    def _append_leaves(self, left_side, right_side):
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
                self._append_leaves(left_side, right_side)
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
                self._append_leaves(left_side, right_side)
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


class ConjunctionOperator(Expression):
    """ Class to perform AND operation for the inputs """

    def __init__(self, left_child, right_child):
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        return (left_side + [self.left_child, self.right_child], right_side),

    def _right_side(self, left_side, right_side):
        return (left_side, right_side + [self.left_child]), \
            (left_side, right_side + [self.right_child])

    def __str__(self):
        return f"({self.left_child} ^ {self.right_child})"

    def equals(self, other):
        return self.left_child == other.left_child and self.right_child == other.right_child


class DisjunctionOperator(Expression):
    """ Class to perform OR operation for the inputs """

    def __init__(self, left_child, right_child):
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        return (left_side + [self.left_child], right_side), \
            (left_side + [self.right_child], right_side)

    def _right_side(self, left_side, right_side):
        return (left_side, right_side + [self.left_child, self.right_child]),

    def __str__(self):
        return f"({self.left_child} v {self.right_child})"

    def equals(self, other):
        return self.left_child == other.left_child and self.right_child == other.right_child


class ImplicationOperator(Expression):
    """ Class to perform implication operation for the inputs """

    def __init__(self, left_child, right_child):
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        return (left_side + [self.right_child], right_side), \
            (left_side, right_side + [self.left_child])

    def _right_side(self, left_side, right_side):
        return (left_side + [self.left_child], right_side + [self.right_child]),

    def __str__(self):
        return f"({self.left_child} => {self.right_child})"

    def equals(self, other):
        return self.left_child == other.left_child and self.right_child == other.right_child


class BiconditionalOperator(Expression):
    """ Class to perform biconditional operation for the inputs """

    def __init__(self, left_child, right_child):
        self.left_child = left_child
        self.right_child = right_child

    def _left_side(self, left_side, right_side):
        return (left_side + [self.left_child, self.right_child], right_side), \
            (left_side, right_side + [self.left_child, self.right_child])

    def _right_side(self, left_side, right_side):
        return (left_side + [self.left_child], right_side + [self.right_child]), \
            (left_side + [self.right_child], right_side + [self.left_child])

    def __str__(self):
        return f"({self.left_child} <=> {self.right_child})"

    def equals(self, other):
        return self.left_child == other.left_child and self.right_child == other.right_child


class NegationOperator(Expression):
    """ Class to perform Negation operation for the inputs """

    def __init__(self, child):
        self.child = child

    def _left_side(self, left_side, right_side):
        return (left_side, right_side + [self.child]),

    def _right_side(self, left_side, right_side):
        return (left_side + [self.child], right_side),

    def __str__(self):
        return f"~{self.child}"


class Proposition(Expression):
    """ Generic class for generating the propositonal variables """

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return str(self.name)

    def equals(self, other):
        return self.name == other.name


def initialize_variables(*prop):
    """ Initializes propositional variables """
    return (Proposition(name) for name in prop)


leaf_list = []
fundamental_list = []
is_fundamental = True
a, b, c, d = initialize_variables('a', 'b', 'c', 'd')
expression = input("Enter the Formula: ")
expression = expression.lower()
prop_expr = eval(expression)
is_tautology = prop_expr.evaluate([], [prop_expr])
if is_tautology:
    print(f"Propotional Formula {prop_expr} is a Tautology")
    print(f"Leaves of the tree: {leaf_list}")
    print(f"Fundamental nodes: {fundamental_list}")
else:
    print(f"Propotional Formula {prop_expr} is NOT a Tautology")
