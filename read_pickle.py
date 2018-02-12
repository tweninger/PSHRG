from __future__ import print_function
import pickle as pkl
import grammar
from sys import argv 

stuff = pkl.load(open(argv[1]))
print(stuff)

