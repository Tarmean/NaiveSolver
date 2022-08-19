import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns





block = [(10, 39945, 96), (20, 86835, 185), (30, 155709, 294), (40, 169557, 341), (50, 196402, 374), (60, 207529, 365), (70, 268917, 517), (80, 289614, 540), (90, 340873, 636), (100, 352541, 648), (110, 413249, 741), (120, 358366, 618), (130, 486888, 863), (140, 486888, 863), (150, 547083, 917), (160, 547083, 917), (170, 638503, 1066), (180, 638503, 1066), (190, 638503, 1066)]
quickXPlain = [(10, 45331, 96), (20, 91991, 185), (30, 155701, 294), (40, 177485, 341), (50, 193541, 374), (60, 194533, 365), (70, 272150, 517), (80, 288061, 540), (90, 345631, 636), (100, 354602, 648), (110, 411154, 741), (120, 346780, 618), (130, 490235, 863), (140, 490235, 863), (150, 530362, 917), (160, 530362, 917), (170, 638151, 1066), (180, 638151, 1066), (190, 638151, 1066)]
deltaDebug_permutation = [(10, 45182, 194), (20, 103176, 363), (30, 171331, 514), (40, 211886, 629), (50, 272256, 738), (60, 377284, 903), (70, 400958, 974), (80, 465836, 1090), (90, 510928, 1162), (100, 550203, 1229), (110, 643560, 1352), (120, 688300, 1389), (130, 756801, 1496), (140, 756801, 1496), (150, 889130, 1674), (160, 889130, 1674), (170, 1079868, 1898), (180, 1079868, 1898), (190, 1079868, 1898)]

example_data = []
for k,v in {'Half Blocking': block, 'QuickXPlain Fixed': quickXPlain, 'Delta Debugging with Permutations': deltaDebug_permutation}.items():
    example_data.extend({'cluster count': pos, 'size': total, 'oracle invocations': its, 'algorithm': k} for i, (pos, total, its) in enumerate(v))

frame = pd.DataFrame(example_data, columns=['cluster count','size', 'oracle invocations', 'algorithm'])
sns.relplot(x='cluster count', y='size', data=frame, kind='line', height=5, aspect=1.5, hue='algorithm')
plt.savefig('plot_graphs_density_1000.png')
