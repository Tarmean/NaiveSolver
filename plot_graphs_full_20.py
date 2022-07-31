import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
import os



quickCheckList = [(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,15),(False,15),(False,15),(False,15),(False,10),(False,10),(False,0)]

smartCheckList = [(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,19),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,18),(False,15),(False,15),(False,15),(False,15),(False,10),(False,10),(False,0)]


full_block = [(False, 10), (False, 10), (False, 15), (False, 15), (False, 15), (False, 15), (False, 17), (False, 18), (False, 17), (False, 18), (False, 17), (False, 18), (False, 17), (False, 18), (False, 18), (False, 19), (False, 18), (False, 19), (False, 18), (False, 19), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
full_block.reverse()



jump2 = [(False, 12), (False, 12), (False, 16), (False, 16), (False, 16), (False, 16), (False, 16), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
jump2.reverse()


quickXPlain = [(False, 0), (False, 10), (False, 10), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 15), (False, 15), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 17), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
quickXPlain.reverse()

quickXPlainBase = [(False, 0), (False, 10), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 10), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19), (False, 15), (False, 17), (False, 18), (False, 19), (False, 19), (False, 19), (False, 18), (False, 19), (False, 19)]
quickXPlainBase.reverse()

deltaDebug = [(True, 20), (False, 10), (False, 10), (False, 15), (False, 15), (False, 15), (False, 15), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 18), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19), (False, 19)]
deltaDebug.reverse()
# example_data = {}
# for k,v in {'smartLoop':smartLoop,'smartCheck':smartCheck}.items():
#     example_data = [{'OracleResult': a, 'tree size': b, 'attempt': i} for i, (a, b) in enumerate(reversed(v))]
#     frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','tree size'])

#     sns.lineplot(x='attempt', y='tree size', data=frame, label=k)


example_data = []
for k,v in {'QuickCheck':quickCheckList,'QuickCheck with Permutations':smartCheckList, 'Half Blocking': full_block, 'Adaptive Delete Blocking': jump2, 'QuickXPlain Fixed': quickXPlain, 'QuickXPlain Paper': quickXPlainBase, 'Delta Debugging': deltaDebug}.items():
     example_data.extend({'OracleResult': a, 'size': b, 'attempt': i, 'algorithm': k} for i, (a, b) in enumerate(reversed(v)))
frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','size', 'algorithm'])
print(frame)
g = sns.lmplot(x='attempt', y='size', col='algorithm', hue='OracleResult', data=frame, palette='muted', fit_reg=False, col_wrap=2)
plt.savefig('scatters_full_20.png')
# sns.lmplot(y='tree size', x='attempt', data=frame, hue='OracleResult', fit_reg=False)

