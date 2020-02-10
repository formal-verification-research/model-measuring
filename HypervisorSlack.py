import spot
import spot.ltsmin
import subprocess
import os
import sys
import argparse
import buddy

#************************************************#
#  Description HypervisorSlack:
#    Initially uses the Make Buchi code for
#    converting the promela model into both a
#    kripke structure and a buchi automaton.
#    This code will then take the same ltl 
#    information and use it to generate a 
#    hypervisor. If no LTL is specified then no
#    hypervisor will be created, as no transitions
#    can be perturbed.
#************************************************#

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
    ltl = args.ltl      #this is the LTL that is to be observed, as well as with which the hypervisor will be made.
else:
    ltl = ''

if args.clean:
    no_path_filename = filename.split('/')[-1]
    ret_code = subprocess.call(['rm', model_name + '_kripke.hoa', model_name + '_kripke.dot', model_name + '_kripke.pdf', model_name + '_buchi.hoa', model_name + '_buchi.dot', model_name + '_buchi.pdf', no_path_filename + '.spins', no_path_filename + '.spins.c', model_name + '_Hypervisor.dot', model_name + '_Hypervisor.pdf', model_name + '_Hypervisor.hoa', model_name + '_Product.dot', model_name + '_Product.hoa', model_name + '_Product.pdf'])
    if ret_code != 0:
        sys.exit(1)
    sys.exit(0)

print("--------Generating Buchi Automaton with specified ltl--------")
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

#***********************************************************************************************************
#  End of MakeBuchi, this is where the hypervisor generation begins. 
#***********************************************************************************************************

    #TODO:
    #make the hypervisor Buchi
    #Look into the spot product function
        #how did thakur do it?
        #How does it work?
        #How can we use it?
    #Look into compositions - how does that work? composing models
        #could we compose the hypervisor with the model
        #then make it a weighted automaton?



# A reference for creating automaton via spot can be found at:
# https://spot.lrde.epita.fr/tut22.html

print("")
print("--------Generating Hypervisor with specified ltl--------")

# creates the dictionary which maintains the correspondance between the
# atomic propositions and the Boolean decision diagram (bdd) variables that 
# label the edges of the automaton.
bdict = spot.make_bdd_dict();

#makes an empty automaton 
buchiHypervisor = spot.make_twa_graph(buchi.get_dict()); 

str_atomic_propositions = " ".join([str(elem) for elem in atomic_propositions])
print(str_atomic_propositions)
print("")

#true = buddy.bdd_ithvar(buchiHypervisor.register_ap("true"))
label = buddy.bdd_ithvar(buchiHypervisor.register_ap(str_atomic_propositions))
#notLabel = buddy.bdd_ithvar(buchiHypervisor.register_ap(str_atomic_propositions))
#transitionLabel = buddy.bdd_ithvar(buchiHypervisor.register_ap("transition"))

buchiHypervisor.set_generalized_buchi(2)

buchiHypervisor.new_states(2)

buchiHypervisor.set_init_state(0)

buchiHypervisor.new_edge(0,0, buddy.bddtrue)
buchiHypervisor.new_edge(0,1, label)
buchiHypervisor.new_edge(1,1, label)
buchiHypervisor.new_edge(1,0, buddy.bddtrue)

print(buchiHypervisor.to_str('hoa'))

buchiHypervisor.save(model_name + '_Hypervisor.hoa')
buchiHypervisor.save(model_name + '_Hypervisor.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_Hypervisor.dot', '-o', model_name + '_Hypervisor.pdf'])
if ret_code == 0:
    print('Human readable Buchi automaton saved at ' + model_name + '_Hypervisor.pdf')
 

product = spot.product(buchiHypervisor, buchi)

product.save(model_name + '_Product.hoa')
product.save(model_name + '_Product.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_Product.dot', '-o', model_name + '_Product.pdf'])
if ret_code == 0:
    print('Human readable Buchi automaton saved at ' + model_name + '_Product.pdf')

#Can we just use a single transition to change from the idle state to the faulty state?
#Can't we have several places that could transition into an area where we would want to be faulty?
