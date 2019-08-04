import argparse
import spot
import buddy
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
        help='Add an erroneous behavior to the hypervisor. See documentation for details.')

args = parser.parse_args()

idDict = {}


#TODO: fill this entry with another set of command line options
#idDict['idle']

for i in range (1, len(args.behavior) + 1):
    split_behavior = args.behavior[i-1].split(',')
    idDict[split_behavior[0]] = dict({'state_num' : i, 
        'type' : split_behavior[1], 
        'reach_from' : split_behavior[2], 
        'ap' : split_behavior[3], 
        'weight' : split_behavior[4]})

# important stuff for making a wtAutomaton (will need to work with model)
hAut = wtAutomaton(spot.make_bdd_dict())

hAut.new_states(len(idDict) + 1)
hAut.prop_state_acc(True)

# Loop though the dictionary and create the behaviors
# this will require parsing of reachability list and creation of aps as done in ModelMeasureMain.py
# form of an edge hAut.new_wt_edge(<from>, <to>, <ap>, weight=<weight>)
# still need to consider edges back to initial state. maybe a -r with a list of states that go back to initial state?

ap_transitions = {}

for behavior in idDict:
    reach_list = behavior['reach_from'].split(':')
    current_ap = buddy.bdd_ithvar(hAut.register_ap(behavior['ap']))
    ap_transitions[behavior['state_num']] = current_ap
    for an_id in reach_list:
        # the form of ap in a weigthed edge may require some additional trickery
        #TODO: remove this if-else once idle state is defined.
        if an_id == 'idle'
            hAut.new_wt_edge(0, behavior['state_num'], current_ap, weight=int(behavior['weight']))
        else:
            hAut.new_wt_edge(idDict[an_id]['state_num'], behavior['state_num'], current_ap, weight=int(behavior['weight']))

print(dir(hAut))











