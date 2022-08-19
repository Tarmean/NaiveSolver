import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
import os



quickCheckList = [(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,15),(False,15),(False,15),(False,15),(False,10),(False,10),(False,0)]

smartCheckList = [(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,15),(False,15),(False,15),(False,15),(False,10),(False,10),(False,0)]


full_block = [(False, 10), (False, 10), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
full_block.reverse()



jump2 = [(False, 10), (False, 10), (False, 17), (False, 13), (False, 17), (False, 13), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
jump2.reverse()


quickXPlain = [(False, 0), (False, 10), (False, 10), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
quickXPlain.reverse()

quickXPlainBase = [(False, 0), (False, 10), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 10), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19)]
quickXPlainBase.reverse()

deltaDebug = [(False, 10), (False, 10), (False, 15), (False, 15), (False, 15), (False, 15), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
deltaDebug.reverse()

deltaDebug_permutation = [(False, 10), (False, 10), (False, 15), (False, 15), (False, 15), (False, 15), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
deltaDebug_permutation.reverse()
# example_data = {}
# for k,v in {'smartLoop':smartLoop,'smartCheck':smartCheck}.items():
#     example_data = [{'OracleResult': a, 'tree size': b, 'attempt': i} for i, (a, b) in enumerate(reversed(v))]
#     frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','tree size'])

#     sns.lineplot(x='attempt', y='tree size', data=frame, label=k)


example_data = []
print("full 20")
print("|Algorithm | Steps |Total|")
print("|-|-|-|")
for k,v in {'QuickCheck':quickCheckList,'QuickCheck with Permutations':smartCheckList, 'Half Blocking': full_block, 'Crit Blocking': jump2, 'QuickXPlain Fixed': quickXPlain, 'QuickXPlain Paper': quickXPlainBase, 'Delta Debugging': deltaDebug, 'Delta Debugging with Permutations': deltaDebug_permutation}.items():
     length = len(v)
     total = sum(a[1] for a in v)
     if length > 0:
         print("|", k, "|", length, "|", total, "|")
     example_data.extend({'OracleResult': a, 'size': b, 'attempt': i, 'algorithm': k} for i, (a, b) in enumerate(reversed(v)))
frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','size', 'algorithm'])
g = sns.lmplot(x='attempt', y='size', col='algorithm', hue='OracleResult', data=frame, palette='muted', fit_reg=False, col_wrap=2)
plt.savefig('scatters_full_20.png')
# sns.lmplot(y='tree size', x='attempt', data=frame, hue='OracleResult', fit_reg=False)

