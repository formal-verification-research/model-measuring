import spot
import spot.ltsmin
import subprocess
import os
import sys
import argparse

#TODO Process killed by linux kernel probably for excessive memory use
#TODONE By using medium or small optimization in postprocess

parser = argparse.ArgumentParser(description='turn a promela specification into a buchi automaton')
parser.add_argument('filename', 
        metavar='<filename>', 
        type=str, 
        nargs=1, 
        help='The promela specification to be used')
parser.add_argument('--ltl', 
        default='NULL', 
        help='The LTL formula to be checked. If none is specified, a comprehensive (and large) automaton will be made')
parser.add_argument('-c', '--clean', 
        action='store_true', 
        help='Clean the files made by previous runs. Requires specification of the model used in the previous run.')

args = parser.parse_args()

filename = args.filename[0]
model_name = filename[0:-4]
if args.ltl != 'NULL':
    ltl = args.ltl
else:
    ltl = ''

if args.clean:
    no_path_filename = filename.split('/')[-1]
    ret_code = subprocess.call(['rm', model_name + '_kripke.hoa', model_name + '_kripke.dot', model_name + '_kripke.pdf', model_name + '_buchi.hoa', model_name + '_buchi.dot', model_name + '_buchi.pdf', no_path_filename + '.spins', no_path_filename + '.spins.c'])
    if ret_code != 0:
        sys.exit(1)
    sys.exit(0)

#*****************************************************#
# Parses the LTL to extract useful atomic propositions.
#*****************************************************#
comparison_symbols=['==', '!=', '>=', '<=', '>', '<']
separated_ltl = []
atomic_propositions = []

ltl = ltl.split('(')
for part in ltl:
    separated_ltl += part.split(')')

for part in separated_ltl:
    try:
        words = part.split(' ')
        if words[1] in comparison_symbols:
            atomic_propositions.append(part)
    except:
        print("Ignoring " + part.join(' '))

#***********************************************************#
# spot takes care of the automaton conversion beginning here.
#***********************************************************#
spot.ltsmin.require('spins')
spot.setup() 

# Compile the promela file
model = spot.ltsmin.load(filename)

# The argument taken here is the atomic proposition(s) to observe in a python list
print("Making kripke with atomic propositions:")
print(atomic_propositions)
k = model.kripke(atomic_propositions)
print("Done making kripke")

# Save the kripke structure
k.save(model_name + '_kripke.hoa')
k.save(model_name + '_kripke.dot','dot')

print("Begining buchi conversion. This may take some time")
buchi = spot.automaton(model_name + '_kripke.hoa').postprocess('BA', 'Low', 'Small')
dead = spot.remove_ap()
dead.add_ap("dead")
buchi = dead.strip(buchi)
print("Finished buchi conversion")

buchi.save(model_name + '_buchi.hoa')
buchi.save(model_name + '_buchi.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_buchi.dot', '-o', model_name + '_buchi.pdf'])
if ret_code == 0:
    print('Human readable Buchi automaton saved at ' + model_name + '_buchi.pdf')

ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_kripke.dot', '-o', model_name + '_kripke.pdf'])
if ret_code == 0:
    print('Human readable Kripke structure saved at ' + model_name + '_kripke.pdf')
