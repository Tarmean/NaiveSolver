import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns

smartLoop = [(True,11),(True,12),(True,14),(True,17),(False,11),(True,18),(True,19),(True,20),(True,23),(False,18),(True,24),(True,31),(True,38),(True,39),(True,41),(True,44),(False,38),(True,45),(True,46),(True,48),(True,51),(False,45),(True,52),(True,53),(True,55),(True,58),(False,52),(True,59),(True,60),(True,61),(True,64),(False,59),(True,65),(True,66),(True,67),(True,68),(True,70),(False,66),(True,71),(False,71),(True,72),(True,73),(False,73),(True,74),(False,74),(True,75),(False,75),(True,76),(False,76),(True,77),(False,77),(True,79),(False,79),(True,80),(True,82),(False,83),(True,84),(True,87),(False,87),(True,90),(False,90),(True,93),(False,93),(True,96),(False,97),(True,99),(True,103),(False,103),(True,107),(False,105),(True,110),(False,110),(True,116),(False,116),(True,119),(True,126),(False,126),(True,133),(False,133),(True,137),(True,144),(False,143),(False,144),(False,142),(True,151),(False,152),(True,155),(True,160),(True,170),(False,169),(True,181),(False,182),(True,196),(False,196),(True,211),(False,208),(True,228),(False,226),(True,253),(False,259),(False,282),(True,290),(True,305),(True,336),(False,354),(True,371),(False,352),(False,382),(True,406),(False,438),(True,453),(True,484),(False,476),(False,484),(True,546),(False,563),(False,608),(True,625),(True,660),(True,729),(False,767),(True,806),(True,884),(False,906),(False,861),(False,876),(False,845),(False,876),(False,813),(False,875),(False,750),(False,751),(False,751),(False,501)]

smartCheck = [(False,8),(False,8),(False,8),(False,8),(False,7),(False,7),(False,8),(False,8),(False,8),(False,7),(False,8),(False,8),(False,7),(False,6),(False,4),(False,5),(True,9),(False,9),(False,8),(False,9),(False,9),(False,8),(False,7),(False,9),(False,9),(False,9),(False,8),(False,9),(False,9),(False,8),(False,7),(False,5),(False,5),(True,10),(False,10),(False,8),(False,10),(False,10),(False,9),(False,7),(False,10),(False,10),(False,10),(False,9),(False,10),(False,10),(False,9),(False,8),(False,6),(False,5),(True,11),(False,10),(False,9),(False,11),(False,11),(False,10),(False,7),(False,11),(False,11),(False,11),(False,10),(False,11),(False,11),(False,10),(False,9),(False,7),(False,5),(True,12),(False,12),(False,11),(False,10),(False,8),(False,12),(False,12),(False,12),(False,11),(False,12),(False,12),(False,11),(False,10),(False,8),(False,5),(True,13),(False,13),(False,11),(False,10),(False,9),(False,13),(False,13),(False,13),(False,12),(False,13),(False,13),(False,12),(False,11),(False,9),(False,5),(True,14),(False,13),(False,12),(False,10),(False,10),(False,14),(False,14),(False,14),(False,13),(False,14),(False,14),(False,13),(False,12),(False,10),(False,5),(True,15),(False,13),(False,13),(False,10),(False,11),(False,15),(False,15),(False,15),(False,14),(False,15),(False,15),(False,14),(False,13),(False,11),(False,5),(True,16),(False,15),(False,16),(False,16),(False,14),(False,16),(False,16),(False,15),(False,13),(False,11),(False,6),(True,17),(False,16),(False,15),(False,17),(False,17),(False,16),(False,13),(False,11),(False,7),(True,18),(False,18),(False,17),(False,16),(False,14),(False,11),(False,8),(True,19),(False,19),(False,17),(False,16),(False,15),(False,11),(False,9),(True,20),(False,19),(False,18),(False,16),(False,16),(False,11),(False,10),(True,21),(False,19),(False,19),(False,16),(False,17),(False,11),(False,11),(True,22),(True,23),(True,25),(True,29),(True,37),(True,53),(True,84),(True,85),(True,87) ,(False,87),(True,88),(False,86),(True,90),(True,98),(False,97),(True,113),(False,82),(True,144),(True,145),(True,147),(True,151),(True,152),(False,152),(True,154),(False,150),(True,158),(True,173),(False,173),(True,204),(False,142),(True,267),(True,268),(True,270),(True,274),(True,282),(True,298),(True,299),(False,299),(False,298),(True,300),(True,304),(False,303),(True,311),(False,296),(True,327),(False,326),(True,389),(True,390),(True,392),(True,396),(False,403),(True,404),(True ,406),(False,406),(True,410),(False,402),(True,418),(True,449),(False,448),(False,386),(False,386),(False,261),(True,511),(True,512),(True,514),(True,518),(True,526),(True,542),(True,573),(True,574),(True,576),(False,576),(True,577),(False,575),(True,579),(True,587),(False,586),(True,602),(False,571),(True,633),(True,634), (True,636),(True,640),(True,641),(False,641),(True,643),(False,639),(True,647),(True,662),(False,662),(True,693),(False,631),(True,756),(True,757),(True,759),(True,763),(True,771),(True,787),(True,788),(False,788),(False,787),(True,789),(True,793),(False,792),(True,800),(False,785),(True,816),(False,815),(True,878),(True,879),(True,881),(True,885),(False,892),(True,893),(True,895),(False,895),(True,899),(False,891),(True,907),(True,938),(False,937),(False,875),(False,875),(False,750),(False,750),(False,500),(False,500)]

quickCheck = [(False,8),(False,8),(False,8),(False,8),(False,7),(False,7),(False,8),(False,8),(False,8),(False,7),(False,8),(False,8),(False,7),(False,6),(False,4),(False,5),(True,9),(False,9),(False,9),(False,8),(False,9),(False,9),(False,8),(False,7),(False,9),(False,9),(False,9),(False,8),(False,9),(False,9),(False,8),(False,7),(False,5),(False,5),(True,10),(False,11),(False,8),(False,11),(False,11),(False,10),(False,7),(False,11),(False,11),(False,11),(False,10),(False,11),(False,11),(False,10),(False,9),(False,7),(False,5),(True,12),(False,15),(False,8),(False,15),(False,15),(False,14),(False,7),(False,15),(False,15),(False,15),(False,14),(False,15),(False,15),(False,14),(False,13),(False,11),(False,5),(True,16),(False,16),(False,23),(False,8),(False,23),(False,23),(False,22),(False,7),(False,23),(False,23),(False,23),(False,22),(False,23),(False,23),(False,22),(False,21),(False,19),(False,5),(True,24),(False,23),(False,38),(False,8),(False,38),(False,38),(False,37),(False,7),(False,38),(False,38),(False,38),(False,37),(False,38),(False,38),(False,37),(False,36),(False,34),(False,5),(True,39),(False,69),(False,8),(False,69),(False,69),(False,68),(False,7),(False,69),(False,69),(False,69),(False,68),(False,69),(False,69),(False,68),(False,67),(False,65),(False,5),(True,70),(False,132),(False,8),(False,132),(False,132),(False,131),(False,7),(False,132),(False,132),(False,132),(False,131),(False,132),(False,132),(False,131),(False,130),(False,128),(False,5),(True,133),(False,133),(False,132),(False,9),(False,133),(False,133),(False,132),(False,7),(False,133),(False,133),(False,133),(False,132),(False,133),(False,133),(False,132),(False,131),(False,129),(False,5),(True,134),(False,134),(False,132),(False,11),(False,135),(False,135),(False,134),(False,7),(False,135),(False,135),(False,135),(False,134),(False,135),(False,135),(False,134),(False,133),(False,131),(False,5),(True,136),(False,132),(False,15),(False,139),(False,139),(False,138),(False,7),(False,139),(False,139),(False,139),(False,138),(False,139),(False,139),(False,138),(False,137),(False,135),(False,5),(True,140),(False,132),(False,23),(False,147),(False,147),(False,146),(False,7),(False,147),(False,147),(False,147),(False,146),(False,147),(False,147),(False,146),(False,145),(False,143),(False,5),(True,148),(False,147),(False,132),(False,38),(False,162),(False,162),(False,161),(False,7),(False,162),(False,162),(False,162),(False,161),(False,162),(False,162),(False,161),(False,160),(False,158),(False,5),(True,163),(False,163),(False,132),(False,69),(False,193),(False,193),(False,192),(False,7),(False,193),(False,193),(False,193),(False,192),(False,193),(False,193),(False,192),(False,191),(False,189),(False,5),(True,194),(False,132),(False,132),(False,256),(False,256),(False,255),(False,7),(False,256),(False,256),(False,256),(False,255),(False,256),(False,256),(False,255),(False,254),(False,252),(False,5),(True,257),(False,257),(False,257),(False,256),(False,255),(False,8),(False,257),(False,257),(False,257),(False,256),(False,257),(False,257),(False,256),(False,255),(False,253),(False,5),(True,258),(False,259),(False,256),(False,255),(False,10),(False,259),(False,259),(False,259),(False,258),(False,259),(False,259),(False,258),(False,257),(False,255),(False,5),(True,260),(False,260),(False,263),(False,256),(False,255),(False,14),(False,263),(False,263),(False,263),(False,262),(False,263),(False,263),(False,262),(False,261),(False,259),(False,5),(True,264),(False,263),(False,270),(False,256),(False,255),(False,21),(False,270),(False,270),(False,270),(False,269),(False,270),(False,270),(False,269),(False,268),(False,266),(False,5),(True,271),(False,286),(False,256),(False,255),(False,37),(False,286),(False,286),(False,286),(False,285),(False,286),(False,286),(False,285),(False,284),(False,282),(False,5),(True,287),(False,318),(False,256),(False,255),(False,69),(False,318),(False,318),(False,318),(False,317),(False,318),(False,318),(False,317),(False,316),(False,314),(False,5),(True,319),(False,318),(False,380),(False,256),(False,255),(False,131),(False,380),(False,380),(False,380),(False,379),(False,380),(False,380),(False,379),(False,378),(False,376),(False,5),(True,381),(False,380),(False,257),(False,255),(False,132),(False,381),(False,381),(False,381),(False,380),(False,381),(False,381),(False,380),(False,379),(False,377),(False,5),(True,382),(False,382),(False,380),(False,259),(False,255),(False,134),(False,383),(False,383),(False,383),(False,382),(False,383),(False,383),(False,382),(False,381),(False,379),(False,5),(True,384),(False,384),(False,380),(False,263),(False,255),(False,138),(False,387),(False,387),(False,387),(False,386),(False,387),(False,387),(False,386),(False,385),(False,383),(False,5),(True,388),(False,380),(False,271),(False,255),(False,146),(False,395),(False,395),(False,395),(False,394),(False,395),(False,395),(False,394),(False,393),(False,391),(False,5),(True,396),(False,380),(False,287),(False,255),(False,162),(False,411),(False,411),(False,411),(False,410),(False,411),(False,411),(False,410),(False,409),(False,407),(False,5),(True,412),(False,411),(False,380),(False,318),(False,255),(False,193),(False,442),(False,442),(False,442),(False,441),(False,442),(False,442),(False,441),(False,440),(False,438),(False,5),(True,443),(False,442),(False,380),(False,380),(False,255),(False,255),(False,504),(False,504),(False,504),(False,503),(False,504),(False,504),(False,503),(False,502),(False,500),(False,5),(True,505),(False,505),(False,505),(False,504),(False,505),(False,503),(False,505),(False,505),(False,504),(False,502),(False,500),(False,6),(True,506),(False,506),(False,507),(False,504),(False,507),(False,503),(False,507),(False,507),(False,506),(False,502),(False,500),(False,8),(True,508),(False,508),(False,511),(False,504),(False,511),(False,503),(False,511),(False,511),(False,510),(False,502),(False,500),(False,12),(True,512),(False,512),(False,519),(False,504),(False,519),(False,503),(False,519),(False,519),(False,518),(False,502),(False,500),(False,20),(True,520),(False,520),(False,535),(False,504),(False,535),(False,503),(False,535),(False,535),(False,534),(False,502),(False,500),(False,36),(True,536),(False,535),(False,566),(False,504),(False,566),(False,503),(False,566),(False,566),(False,565),(False,502),(False,500),(False,67),(True,567),(False,567),(False,566),(False,505),(False,567),(False,503),(False,567),(False,567),(False,566),(False,502),(False,500),(False,68),(True,568),(False,566),(False,507),(False,569),(False,503),(False,569),(False,569),(False,568),(False,502),(False,500),(False,70),(True,570),(False,566),(False,511),(False,573),(False,503),(False,573),(False,573),(False,572),(False,502),(False,500),(False,74),(True,574),(False,574),(False,566),(False,519),(False,581),(False,503),(False,581),(False,581),(False,580),(False,502),(False,500),(False,82),(True,582),(False,581),(False,566),(False,534),(False,596),(False,503),(False,596),(False,596),(False,595),(False,502),(False,500),(False,97),(True,597),(False,566),(False,565),(False,627),(False,503),(False,627),(False,627),(False,626),(False,502),(False,500),(False,128),(True,628),(False,628),(False,627),(False,504),(False,628),(False,628),(False,627),(False,502),(False,500),(False,129),(True,629),(False,629),(False,627),(False,506),(False,630),(False,630),(False,629),(False,502),(False,500),(False,131),(True,631),(False,627),(False,510),(False,634),(False,634),(False,633),(False,502),(False,500),(False,135),(True,635),(False,627),(False,518),(False,642),(False,642),(False,641),(False,502),(False,500),(False,143),(True,643),(False,642),(False,627),(False,533),(False,657),(False,657),(False,656),(False,502),(False,500),(False,158),(True,658),(False,658),(False,627),(False,564),(False,688),(False,688),(False,687),(False,502),(False,500),(False,189),(True,689),(False,627),(False,627),(False,751),(False,751),(False,750),(False,502),(False,500),(False,252),(True,752),(False,752),(False,752),(False,751),(False,750),(False,503),(False,500),(False,253),(True,753),(False,754),(False,751),(False,750),(False,505),(False,500),(False,255),(True,755),(False,755),(False,758),(False,751),(False,750),(False,509),(False,500),(False,259),(True,759),(False,758),(False,765),(False,751),(False,750),(False,516),(False,500),(False,266),(True,766),(False,781),(False,751),(False,750),(False,532),(False,500),(False,282),(True,782),(False,813),(False,751),(False,750),(False,564),(False,500),(False,314),(True,814),(False,813),(False,875),(False,751),(False,750),(False,626),(False,500),(False,376),(True,876),(False,875),(False,752),(False,750),(False,627),(False,500),(False,377),(True,877),(False,877),(False,875),(False,754),(False,750),(False,629),(False,500),(False,379),(True,879),(False,879),(False,875),(False,758),(False,750),(False,633),(False,500),(False,383),(True,883),(False,875),(False,766),(False,750),(False,641),(False,500),(False,391),(True,891),(False,875),(False,782),(False,750),(False,657),(False,500),(False,407),(True,907),(False,906),(False,875),(False,813),(False,750),(False,688),(False,500),(False,438),(True,938),(False,937),(False,875),(False,875),(False,750),(False,750),(False,500),(False,500)]
# smartLoop = [(True,2),(True,3),(True,5),(True,7),(True,11),(False,12),(True,13),(False,13),(True,14),(True,15),(False,17),(False,13),(False,17),(True,20),(False,14),(True,26),(True,51)]
# smartLoop = [(False,12),(True,13),(True,14),(True,16),(False,16),(True,19),(True,20),(False,20),(True,25),(False,21),(False,15),(True,27),(True,51)]
# quickCheck = [(False,1),(False,1),(True,2),(False,2),(False,1),(True,3),(False,2),(False,3),(False,1),(True,4),(False,6),(False,1),(True,7),(False,13),(False,1),(True,14),(False,13),(False,3),(True,16),(False,16),(False,13),(False,6),(True,19),(False,19),(False,13),(False,12),(True,25),(True,50)]

example_data = []
print("tree 1000")
print("|Algorithm | Steps |Total|")
print("|-|-|-|")
for k,v in {'QuickCheck':quickCheck,'QuickCheck with Permutations':smartCheck, 'Adaptive Delete Blocking': smartLoop}.items():
     length = len(v)
     total = sum(a[1] for a in v)
     if length > 0:
         print("|", k, "|", length, "|", total, "|")
     example_data.extend({'Oracle Result': a, 'size': b, 'attempt': i, 'algorithm': k} for i, (a, b) in enumerate(reversed(v)))
frame = pd.DataFrame(example_data, columns=['attempt','Oracle Result','size', 'algorithm'])
g = sns.lmplot(x='attempt', y='size', col='algorithm', hue='Oracle Result', data=frame, palette='muted', fit_reg=False, col_wrap=1)
plt.savefig('scatters_tree_1000.png')
