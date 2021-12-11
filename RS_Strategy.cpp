#include <iostream>
#include <string>
#include <stack>
#include <map>
#include <iomanip>

#define CONJUNCT '^'
#define DISJUNCT 'v'
#define IMPLICATE '>'
#define NEGATION '~'
#define PLACEHOLDER_C '#'
#define PLACEHOLDER_S "#"
#define DELIMITER "------------------------------"

using namespace std;

// set priority for logic operators
map<char, int> prior = { {CONJUNCT, 1}, {DISJUNCT, 1}, {IMPLICATE, 1}, {NEGATION, 2} };
// two vectors storing formulas and negative formulas
string pos, neg;
// two global parameters
bool fundamental = false;
bool tautology = true;

// tree class
template<class T> class TreeNode
{
public:
	T value;
	TreeNode* left;
	TreeNode* right;

	TreeNode(T x)
	{
		value = x;
		left = nullptr;
		right = nullptr;
	}

	TreeNode()
	{
		value = 0;
		left = nullptr;
		right = nullptr;
	}
};

// transform to reverse polish notation
string ReversePolishNotation(string raw)
{
	char c_tmp;
	string reverse_polish, s_tmp;
	stack<char> st;
	int len = raw.length();

	for (int i = 0; i < len; i++)
	{
		c_tmp = raw[i];

		// ( or [, push operator into stack
		if (c_tmp == '(' || c_tmp == '[')
			st.push(c_tmp);
		// ), pop operator until (
		else if (c_tmp == ')')
		{
			while (st.top() != '(')
			{
				s_tmp = st.top();
				reverse_polish.append(s_tmp);
				st.pop();
			}
			st.pop();
		}
		// ], pop operator until [
		else if (c_tmp == ']')
		{
			while (st.top() != '[')
			{
				s_tmp = st.top();
				reverse_polish.append(s_tmp);
				st.pop();
			}
			st.pop();
		}
		// pop stack until priority lower, then push operator into stack
		else if (prior[c_tmp] >= 1)
		{
			while (!st.empty() && prior[st.top()] >= prior[c_tmp])
			{
				s_tmp = st.top();
				reverse_polish.append(s_tmp);
				st.pop();
			}
			st.push(c_tmp);
			// add a prefix for negation
			if (c_tmp == NEGATION)
				reverse_polish.append(PLACEHOLDER_S);
		}
		// put formulas into string
		else
		{
			s_tmp = c_tmp;
			reverse_polish.append(s_tmp);
		}
	}
	// put rest of the operators into string
	while (!st.empty())
	{
		s_tmp = st.top();
		reverse_polish.append(s_tmp);
		st.pop();
	}
	return reverse_polish;
}

// transform to binary tree
TreeNode<char>* buildTree(string s)
{
	TreeNode<char>* tn = new TreeNode<char>;

	// empty tree error
	if (s.length() == 0)
	{
		cout << endl << "The tree is empty!" << endl;
		return tn;
	}

	char c_tmp;
	stack<TreeNode<char>*> st;

	for (int i = 0; i < s.length(); i++)
	{
		c_tmp = s[i];
		tn = new TreeNode<char>;
		// operator
		if (prior[c_tmp] >= 1)
		{
			// right
			TreeNode<char>* tn_tmp = st.top();
			tn->right = tn_tmp;
			st.pop();
			// left
			tn_tmp = st.top();
			tn->left = tn_tmp;
			st.pop();
		}
		// value
		tn->value = c_tmp;
		st.push(tn);
	}
	
	return tn;
}

// copy binary tree
void copyTree(TreeNode<char>* ori_tree, TreeNode<char>* new_tree)
{
	if (!ori_tree)
		return;
	else
	{
		new_tree->value = ori_tree->value;
		if (ori_tree->left)
			new_tree->left = new TreeNode<char>;
		if (ori_tree->right)
			new_tree->right = new TreeNode<char>;
		copyTree(ori_tree->left, new_tree->left);
		copyTree(ori_tree->right, new_tree->right);
	}
}

// copy the changed seq to the left node of seqs tree
void addSeqsTreeLeft(TreeNode<TreeNode<char>*>* seqs)
{
	seqs->left = new TreeNode<TreeNode<char>*>;
	seqs->left->value = new TreeNode<char>;
	copyTree(seqs->value, seqs->left->value);
}

// shared code for conjunction and disjunction under negation
void sharedCode(TreeNode<char>* seq, TreeNode<TreeNode<char>*>* seqs)
{
	// second layer
	seq->left->value = NEGATION;
	seq->right->value = NEGATION;
	seq->left->left = new TreeNode<char>;
	seq->left->right = seq->right->left;
	seq->right->left = new TreeNode<char>;
	// third layer
	seq->left->left->value = PLACEHOLDER_C;
	seq->right->left->value = PLACEHOLDER_C;
	// change
	addSeqsTreeLeft(seqs);
	// return back
	delete(seq->right->left);
	seq->right->left = seq->left->right;
	seq->left->right = nullptr;
	delete(seq->left->left);
	seq->left->value = PLACEHOLDER_C;
	seq->value = NEGATION;
}

// RS Method
void RSMethod(TreeNode<char>* seq_prev, int branch, TreeNode<TreeNode<char>*>* seqs)
{
	// decide the branch
	TreeNode<char>* seq = nullptr;
	if (branch == -1)  // left branch
		seq = seq_prev->left;
	else if (branch == 1)  // right branch
		seq = seq_prev->right;
	else if (branch == 0)  // root
		seq = seq_prev;

	// judge the current operator
	if (seq->value == NEGATION)
	{
		if (seq->right->value == NEGATION)
		{
			if (branch == -1)  // left branch
			{
				seq_prev->left = seq->right->right;
				addSeqsTreeLeft(seqs);
				seq_prev->left = seq;
			}
			else if (branch == 1)  // right branch
			{
				seq_prev->right = seq->right->right;
				addSeqsTreeLeft(seqs);
				seq_prev->right = seq;
			}
			else if (branch == 0)  // root
			{
				
				seqs->value = seq->right->right;
				addSeqsTreeLeft(seqs);
				seqs->value = seq;
			}
		}
		else if (seq->right->value == IMPLICATE)
		{
			// first layer
			seq->value = CONJUNCT;
			delete(seq->left);
			seq->left = seq->right->left;
			// second layer
			seq->right->value = NEGATION;
			seq->right->left = new TreeNode<char>;
			// third layer
			seq->right->left->value = PLACEHOLDER_C;
			// change
			addSeqsTreeLeft(seqs);
			// return back
			delete(seq->right->left);
			seq->right->left = seq->left;
			seq->right->value = IMPLICATE;
			seq->left = new TreeNode<char>;
			seq->left->value = PLACEHOLDER_C;
			seq->value = NEGATION;
		}
		else if (seq->right->value == CONJUNCT)
		{
			seq->value = DISJUNCT;  // first layer
			sharedCode(seq, seqs);
			seq->right->value = CONJUNCT;
		}
		else if (seq->right->value == DISJUNCT)
		{
			seq->value = CONJUNCT;  // first layer
			sharedCode(seq, seqs);
			seq->right->value = DISJUNCT;
		}
	}
	else if (seq->value == IMPLICATE)
	{
		// remember the location of left branch
		TreeNode<char>* tmp = seq->left;
		// initialize
		seq->left = new TreeNode<char>;
		seq->left->left = new TreeNode<char>;
		// change
		seq->value = DISJUNCT;
		seq->left->value = NEGATION;
		seq->left->left->value = PLACEHOLDER_C;
		seq->left->right = tmp;
		addSeqsTreeLeft(seqs);
		// return back
		seq->value = IMPLICATE;
		seq->left = tmp;

	}
	else if (seq->value == CONJUNCT)
	{
		// initialize
		seqs->left = new TreeNode<TreeNode<char>*>;
		seqs->left->value = new TreeNode<char>;
		seqs->right = new TreeNode<TreeNode<char>*>;
		seqs->right->value = new TreeNode<char>;

		if (branch == 0)  // root
		{
			copyTree(seq->left, seqs->left->value);
			copyTree(seq->right, seqs->right->value);
		}
		else if (branch == -1)  // left branch
		{
			seq_prev->left = seq->left;
			copyTree(seqs->value, seqs->left->value);
			seq_prev->left = seq->right;
			copyTree(seqs->value, seqs->right->value);
			seq_prev->left = seq;
		}
		else if (branch == 1)  // right branch
		{
			seq_prev->right = seq->left;
			copyTree(seqs->value, seqs->left->value);
			seq_prev->right = seq->right;
			copyTree(seqs->value, seqs->right->value);
			seq_prev->right = seq;
		}
	}
	else if (seq->value == DISJUNCT)
	{
		RSMethod(seq, -1, seqs);
		RSMethod(seq, 1, seqs);
	}
}

// traverse the seqs tree in pre-order to use RS method
void preOrderTraversal(TreeNode<TreeNode<char>*>* seqs)
{
	RSMethod(seqs->value, 0, seqs);
	if (seqs->left)
		preOrderTraversal(seqs->left);
	if (seqs->right)
		preOrderTraversal(seqs->right);
}

// print seq tree
void show(TreeNode<char>* tn, int d)
{
	if (tn)
	{
		show(tn->right, d + 1);
		cout << setw(5 * d) << " " << tn->value << endl;
		show(tn->left, d + 1);
	}
}

// print seq tree in a formula
void show(TreeNode<char>* tn, bool negation)
{
	size_t found = -1;
	if (tn->value == NEGATION && tn->right)
		show(tn->right, true);
	else if (tn->value != NEGATION)
	{
		if (tn->left)
			show(tn->left, false);
		if (tn->value != DISJUNCT)
		{
			if (negation)
			{
				found = pos.find(tn->value);
				if (found != string::npos)
					fundamental = true;
				neg.push_back(tn->value);
			}
			else
			{
				found = neg.find(tn->value);
				if (found != string::npos)
					fundamental = true;
				pos.push_back(tn->value);
			}
		}
		if (tn->right)
			show(tn->right, false);
	}
}

// print leaves of the seqs tree
void show(TreeNode<TreeNode<char>*>* seqs)
{
	if (!seqs->left && !seqs->right)
	{
		cout << endl << "The binary tree for this leaf (# is a placeholder for negation):" << endl;
		show(seqs->value, 0);
		show(seqs->value, false);
		cout << endl << "This leaf: ";
		for (char c : pos)
			cout << c << ", ";
		for (char c : neg)
			cout << NEGATION << c << ", ";
		if (fundamental)
		{
			cout << " (fundamental)" << endl;
			cout << endl << DELIMITER << endl;
		}
		else
		{
			cout << " (NOT fundamental)" << endl;
			cout << endl << DELIMITER << endl;
			tautology = false;
			// clear
			pos.clear();
			neg.clear();
			return;
		}
		// clear
		pos.clear();
		neg.clear();
		fundamental = false;
	}
	if (seqs->left)
	{
		if (!tautology)
			return;
		show(seqs->left);
	}
	if (seqs->right)
	{
		if (!tautology)
			return;
		show(seqs->right);
	}
}

/*
	INPUT: A propositional formula
			~ for Negation
			^ for Conjunction
			v for Disjunction
			-> or > for Implication Operator
			(Spaces are allowed between characters.)
			(Do not input two ~ continuously. Seperate them with parentheses like this: ~(~a).)
	OUTPUT: 1. The binary tree representation for this sequence
			2. The binary tree representation for each leaf
			(The tree grows from the left side to the right side.)
			3. Whether the according leaf is fundamental
			4. Whether this formula is a tautology
	Please follow the instructions shown on the teminal.
	This project does not contain any function for checking grammar error.
*/
int main() {
	
	while (1)
	{
		// 1. input
		cout << endl << "****************************************************************" << endl;
		cout << endl << "Please Enter a Sequence (q for quit):" << endl;
		cout << endl << "(Do not input two ~ continuously. Seperate them with parentheses like this: ~(~a).)" << endl << endl;
		string seq;
		getline(cin, seq);
		if (seq == "q")  // quit
			return 0;

		// 2. clean the input
		seq.erase(remove(seq.begin(), seq.end(), '-'), seq.end());  // erase '-'
		seq.erase(remove(seq.begin(), seq.end(), ' '), seq.end());  // erase ' '

		// 3. seq -> reverse polish notation -> binary tree
		seq = ReversePolishNotation(seq);
		TreeNode<char>* seq_tree = buildTree(seq);
		cout << endl << "The binary tree for this sequence (# is a placeholder for negation):" << endl;
		show(seq_tree, 0);
		cout << endl << DELIMITER << endl;

		// 4. insert this tree into the seqs tree
		TreeNode<TreeNode<char>*>* seqs = new TreeNode<TreeNode<char>*>;
		seqs->value = seq_tree;

		// 5. traverse the seqs tree
		preOrderTraversal(seqs);

		// 6. print all and check whether it is a tautology
		show(seqs);
		if (tautology)
			cout << endl << "** This formula is a tautology." << endl << endl;
		else
			cout << endl << "** One leaf is not fundamental. This formula is NOT a tautology." << endl << endl;

		// 7. be ready for the next round
		delete(seqs);
		tautology = true;
	}

	return 0;
}