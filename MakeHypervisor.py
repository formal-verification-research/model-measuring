import argparse
import spot
import buddy
import subprocess
from Hypervisor import *

parser = argparse.ArgumentParser(description='assisted construction of a hypervisor for a given automaton')

# Each argument should represent one erroneous behavior #

# First potential form of an argument #
# type,reachability,label identifier(s),weight #
# type can be <always, non-deterministic>
# types apply to the beginning event of a behavior.
# subsequent events are taken to be of type "always"
# reachability can be <always, error-states, idle-state>
# label identifiers have the form:
# var<comparison>val->var<comp>val->...

# Second potential form #
# id,type,reachability,label identifier,weight
# all are as above except id is a uint, reachability can be a list of specific ids in addition to the above and label identifiers must be individual.
# id 0 is reserved fo the idle state.
parser.add_argument('-b', '--behavior',
        action='append',
        help='Add an erroneous behavior to the hypervisor. Format <id,type,reachability,ap,weight>')

parser.add_argument('-r', '--reset',
        action='append',
        default=[],
        help='Add a behavior of the same format that returns the model to the idle state.')

args = parser.parse_args()

idDict = {}
resetDict = {}

for i in range(1, len(args.behavior) + 1):
    split_behavior = args.behavior[i-1].split(',')
    idDict[split_behavior[0]] = dict({'state_num' : i,
        'type' : split_behavior[1],
        'reach_from' : split_behavior[2],
        'ap' : split_behavior[3],
        'weight' : split_behavior[4]})

idDict['idle'] = dict({'state_num' : 0})

for behavior in args.reset:
    split_reset = behavior.split(',')
    resetDict[split_reset[0]] =  dict({'state_num' : 0, 
        'type' : split_behavior[1], 
        'reach_from' : split_behavior[2], 
        'ap' : split_behavior[3], 
        'weight' : split_behavior[4]})


# important stuff for making a wtAutomaton (will need to work with model)
hAut = wtAutomaton(spot.make_bdd_dict())

hAut.new_states(len(idDict))
hAut.prop_state_acc(True)

ap_transitions = {}

### Do for all error behaviors ###
for behavior in list(idDict.values()):
    if behavior['state_num'] != 0:
        reach_list = behavior['reach_from'].split(':')
        current_ap = buddy.bdd_ithvar(hAut.register_ap(behavior['ap']))
        ap_transitions[behavior['state_num']] = current_ap
    
        ### Create transitions to this error state ###
        for an_id in reach_list:
            #NOTE: the form of ap in a weigthed edge may require some additional trickery here
            hAut.new_wt_edge(idDict[an_id]['state_num'], behavior['state_num'], current_ap, weight=int(behavior['weight']))
            ### Create the self loops ###
            #TODO: Find out about the vitality of these for deterministic behavior.
            


### Save the created automaton ###
print(hAut.to_str())

with open('test.dot', 'w') as fp:
    fp.write(hAut.to_str('dot'))
fp.close()

subprocess.call(['dot', '-Tpdf', 'test.dot', '-o', 'test.pdf'])








