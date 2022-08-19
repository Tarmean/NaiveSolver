import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
import os



quickCheckList = [(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,8),(False,8),(False,8),(False,8),(False,8),(False,5),(False,5),(False,0),(True,10),(False,9),(False,9),(False,9),(False,9),(False,9),(False,6),(False,6),(False,0),(True,11),(False,9),(False,9),(False,9),(False,9),(False,6),(False,6),(False,0),(True,12),(False,8),(False,8),(False,0),(True,16),(False,16),(False,0),(True,32),(False,0),(True,63),(False,0),(True,125),(False,125),(False,0),(True,250),(False,250),(False,0),(True,500),(False,500),(False,0)]

smartCheckList = [(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,9),(False,8),(False,8),(False,8),(False,8),(False,8),(False,5),(False,5),(False,0),(True,10),(False,10),(True,11),(True,12),(False,12),(False,12),(False,12),(False,12),(False,12),(False,12),(False,12),(False,12),(False,12),(False,12),(True,13),(True,14),(True,16),(False,14),(True,18),(True,24),(False,24),(False,24),(False,24),(True,31),(True,41),(True,54),(True,71),(True,94),(False,63),(True,125),(True,250),(True,500),(False,500),(False,0)]


full_block = [(True, 500), (True, 250), (True, 125), (False, 62), (True, 63), (False, 31), (True, 32), (False, 16), (False, 16), (True, 24), (True, 20), (True, 18), (True, 17), (False, 9), (False, 9), (False, 13), (False, 13), (False, 13), (True, 13), (False, 11), (False, 11), (True, 11), (True, 10), (False, 8), (False, 8), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9)]
full_block.reverse()


jump2 = [(False, 500), (True, 500), (False, 250), (True, 250), (False, 125), (True, 125), (True, 63), (True, 32), (False, 16), (False, 16), (False, 24), (False, 24), (False, 24), (True, 24), (False, 20), (True, 20), (True, 19), (False, 18), (True, 18), (True, 17), (False, 13), (False, 13), (True, 13), (False, 12), (False, 12), (False, 12), (False, 12), (False, 12), (True, 12), (True, 11), (True, 10), (False, 9), (False, 9), (False, 9), (False, 9)]
jump2.reverse()


quickXPlain = [(False, 0), (True, 500), (True, 250), (True, 125), (False, 62), (True, 63), (False, 31), (True, 32), (False, 16), (False, 16), (True, 24), (True, 20), (True, 18), (False, 17), (True, 17), (False, 9), (False, 9), (False, 13), (False, 13), (True, 15), (True, 14), (False, 12), (False, 12), (False, 13), (False, 13), (False, 13), (False, 13), (False, 10), (True, 10), (False, 8), (False, 8), (False, 9), (False, 9), (False, 9), (False, 9)]
quickXPlain.reverse()

quickXPlainBase = [(False, 0), (True, 500), (True, 250), (True, 125), (False, 62), (False, 93), (False, 109), (True, 117), (True, 113), (True, 111), (False, 110), (True, 110), (False, 94), (False, 102), (False, 106), (True, 108), (True, 107), (False, 103), (False, 105), (False, 106), (False, 106), (False, 105), (False, 106), (False, 106), (False, 99), (False, 103), (False, 105), (False, 106), (False, 106), (False, 105), (False, 106), (False, 106), (True, 103), (True, 72), (True, 10)]
quickXPlainBase.reverse()

deltaDebug =[(False, 500), (True, 500), (False, 250), (True, 250), (False, 125), (True, 125), (True, 63), (True, 32), (False, 16), (False, 16), (False, 24), (False, 24), (False, 24), (True, 24), (False, 16), (False, 16), (False, 16), (True, 20), (False, 16), (False, 16), (False, 16), (False, 16), (True, 16), (False, 12), (False, 12), (False, 12), (False, 12), (True, 14), (False, 12), (False, 12), (False, 12), (False, 12), (False, 12), (False, 12), (True, 12), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (True, 11), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (True, 10), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9)]
deltaDebug.reverse()


deltaDebug_permutation = [(False, 500), (True, 500), (True, 250), (True, 125), (False, 63), (True, 63), (True, 32), (False, 16), (False, 16), (False, 24), (False, 24), (False, 24), (True, 24), (False, 16), (False, 16), (False, 16), (True, 20), (False, 16), (False, 16), (False, 16), (False, 16), (True, 16), (False, 12), (False, 12), (False, 12), (False, 12), (True, 14), (False, 12), (False, 12), (False, 12), (False, 12), (False, 12), (False, 12), (True, 12), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (True, 11), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (False, 10), (True, 10), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9), (False, 9)]
deltaDebug_permutation.reverse()
# example_data = {}
# for k,v in {'smartLoop':smartLoop,'smartCheck':smartCheck}.items():
#     example_data = [{'OracleResult': a, 'tree size': b, 'attempt': i} for i, (a, b) in enumerate(reversed(v))]
#     frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','tree size'])

#     sns.lineplot(x='attempt', y='tree size', data=frame, label=k)


example_data = []
print("cluster 1000 10")
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
plt.savefig('scatters_cluster_1000_10.png')
# sns.lmplot(y='tree size', x='attempt', data=frame, hue='OracleResult', fit_reg=False)

