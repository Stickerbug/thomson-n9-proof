"""Reproduce the finite experiment into a fresh output prefix, never overwrite data."""
import argparse,importlib
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prefix',default='sharp_contact_refinement2026_replay_',help='fresh output filename prefix, starting sharp_contact_refinement2026_')
parser.add_argument('--steps',default='contact,refine,export,competitive',help='ordered comma list: diagnostics,contact,refine,export,competitive')
a=parser.parse_args()
assert a.prefix.startswith('sharp_contact_refinement2026_') and all(c.isalnum() or c=='_' for c in a.prefix)
modules={'diagnostics':('core','main'),'contact':('contact_psd','run'),'refine':('refine','run'),'export':('export','main'),'competitive':('competitive','run')}
for step in a.steps.split(','):
    name,fn=modules[step];m=importlib.import_module('sharp_contact_refinement2026_'+name);m.PREFIX=a.prefix
    print('START STEP',step,'fresh output prefix',a.prefix,flush=True);getattr(m,fn)()
