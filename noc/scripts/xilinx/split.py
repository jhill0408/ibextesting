def split(xmin,xmax,ymin,ymax,direction,n,level, start_index):
    m = int(start_index/(2**level))
    print("create_pblock {pblock_level_",level,"_", start_index,"",start_index+2**level,"}",sep='')
    print("resize_pblock [get_pblocks {pblock_level_",level,"_", start_index,"",start_index+2**level,"}] -add {CLOCKREGION_X",xmin,"Y",ymin,":CLOCKREGION_X",xmax,"Y",ymax,"}",sep='')
    for switches in range(2**level):
        if level > 0:
            print("add_cells_to_pblock [get_pblocks {pblock_level_",level,"_", start_index,"",start_index+2**level,"}] [get_cells -quiet [list {n2.ls[",level,"].ms[",m,"].ns[",switches,"].pi_level.sb}]]",sep='')
        else:
            print("add_cells_to_pblock [get_pblocks {pblock_level_",level,"_", start_index,"",start_index+2**level,"}] [get_cells -quiet [list {xs[",start_index+switches,"].pi_level0.sb}]]",sep='')

        #print("Switch", start_index+switches,"at Level", level,"contrained X", xmin, xmax,"constrained y", ymin, ymax)
    if n==1:
        return
    else:
        if (direction==0): #vertical
            split(xmin, xmin+int((xmax-xmin)/2),ymin, ymax,1, int(n/2), level-1, start_index)
            split(xmin+int((xmax-xmin)/2), xmax,ymin, ymax,1, int(n/2), level-1, start_index + (2**(level-1)))
        else: #horizontal
            split(xmin, xmax,ymin, ymin+int((ymax-ymin)/2),0, int(n/2), level-1, start_index)
            split(xmin, xmax,ymin+int((ymax-ymin)/2), ymax,0, int(n/2), level-1, start_index + (2**(level-1)))


import sys
import math
N = int(sys.argv[1])

level=int(math.log2(N))

xmin = 0
xmax = 5
ymin = 0
ymax = 14
start_index=0
split(xmin,xmax,ymin,ymax,1,2**level,level, start_index)
