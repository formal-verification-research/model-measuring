import spot
import spot.ltsmin
import subprocess
import os
import argparse

parser = argparse.ArgumentParser(description='turn a promela specification into a buchi automaton')
parser.add_argument('filename', metavar='<filename>', type=str, nargs=1, help='The promela specification to be used')
parser.add_argument('--ltl', metavar='<ltl>', type=str, nargs=1, help='The LTL formula to be checked')

args = parser.parse_args()

filename = args.filename[0]
ltl = args.ltl[0]

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
            print("entered the append loop")
            atomic_propositions.append(part)
    except:
        print("can't slpit " + part.join(','))


# Confirms spins is installed correctly
spot.ltsmin.require('spins')

# Only needed for displaying structures which is not working natively
spot.setup() 

# Compile the promela file
model = spot.ltsmin.load(filename)

# The argument is the atomic proposition(s) to observe in a list
print("making kripke with atomic propositions:")
print(atomic_propositions)
k = model.kripke(atomic_propositions)
print("done making kripke")

k.save('kripke.hoa')
k.save('kripke.dot','dot')

print("begin buchi conversion")
buchi = spot.automaton('kripke.hoa').postprocess('BA', 'any')
print("finished buchi conversion")

buchi.save('buchi.hoa')
buchi.save('buchi.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', 'buchi.dot', '-o', 'buchi.pdf'])
print("buchi pdf ret_code: " + str(ret_code))

ret_code = subprocess.call(['dot', '-Tpdf', 'kripke.dot', '-o', 'kripke.pdf'])
print("kripke pdf ret_code: " + str(ret_code))
