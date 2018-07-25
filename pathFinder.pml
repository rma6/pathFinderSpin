typedef array
{
	byte c[columns];
};

typedef barray
{
	bit c[columns];
};

typedef larray
{
	byte c[255];
};

typedef coords
{
    byte line, column, direction, cells;
    array reg[lines];
    byte path[255];
    byte pathSize;
    bit ready; //set to 1 when all data is copied to parameters array
};

chan STDIN; //get values in ASCII

array CM[lines], ACM[lines], dead_end_vector_position[lines];
larray dead_ends_paths[255];
byte startLine, startColumn, open_cells, sc, scide, depp, solutionSize, de_preppendSize;
byte solution[255], de_append[255], de_preppend[255];

barray nav_mtxs[lines];
bit m_dep;

coords ic[255];

proctype dead_end_thread(byte line; byte column; chan jch) //jch: join channel
{
    byte i=line, j=column, it;
    byte path[255];
    byte pathp=127, pathl;
    do
    ::  atomic //lock mutex by hardware
        {
            nav_mtxs[i].c[j]==0;
            nav_mtxs[i].c[j]=1;
        }

        if
        ::  i==startLine && j==startColumn && ACM[i].c[j]<3 -> scide=2;
        ::  else -> if
                    ::  i==startLine && j==startColumn && scide<=2 -> scide=scide+1;
                    ::  else -> skip;
                    fi
        fi

        if //dead_end insertion
        ::  dead_end_vector_position[i].c[j]!=0 -> 
                it=0;
                do
                ::  dead_ends_paths[dead_end_vector_position[i].c[j]-1].c[it] != 4 ->
                        path[pathp+pathl] = dead_ends_paths[dead_end_vector_position[i].c[j]-1].c[it];
                        it++;
                        pathl++;
                ::  else -> break;
                od
        ::  else -> skip;
        fi

        if
        ::  ACM[i].c[j]<3 && !(i==startLine && j==startColumn) ->
            byte ti=i, tj=j;
            CM[i].c[j]=1;

            if //navigation
            ::  i-1>=0 && CM[i-1].c[j]==0 ->
                    i--;
                    path[pathp+pathl] = 0;
                    pathl = pathl+2;
                    path[pathp-1]=1;
                    pathp--;

            ::  i+1<lines && CM[i+1].c[j]==0 ->
                    i++;
                    path[pathp+pathl] = 1;
                    pathl = pathl+2;
                    path[pathp-1]=0;
                    pathp--;

            ::  j-1>=0 && CM[i].c[j-1]==0 ->
                    j--;
                    path[pathp+pathl] = 2;
                    pathl = pathl+2;
                    path[pathp-1]=3;
                    pathp--;

            ::  else ->
                    j++;
                    path[pathp+pathl] = 3;
                    pathl = pathl+2;
                    path[pathp-1]=2;
                    pathp--;
            fi
            nav_mtxs[ti].c[tj]=0;
            
        ::  else ->
                if
                ::  else ->
                        ACM[i].c[j]--;
                        atomic //lock mutex by hardware
                        {
                            m_dep==0;
                            m_dep=1;
                        }
                        for(it : 0 .. pathl-1) {
                            dead_ends_paths[depp].c[it]=path[it+pathp];
                        }
                        dead_ends_paths[depp].c[it]=4; //mark end
                        depp++;
                        if
                        ::  it>0 -> dead_end_vector_position[i].c[j]=depp; //0 means no path, then its marked as depp+1 (depp++);
                        ::  else -> skip;
                        fi
                        m_dep=0;
                        nav_mtxs[i].c[j]=0;
                        break;
                fi
        fi
    od
    jch!_pid;
}

proctype dead_end_sc(byte line; byte column; chan jch)
{
    byte i=line, j=column, it, deep;
    byte path[255];
    byte pathp=127, pathl, spathl, prep;

    do
    ::  if
        ::  ACM[i].c[j]<3 ->
                CM[i].c[j]=1;
                if
                ::  dead_end_vector_position[i].c[j]!=0 ->
                        deep=0;
                        do
                        ::  dead_ends_paths[dead_end_vector_position[i].c[j]-1].c[deep] != 4 -> deep++; //find end
                        ::  else -> deep--; break;
                        od
                        do
                        ::  deep!=0 ->
                                pathp--;
                                pathl++;
                                path[pathp] = dead_ends_paths[dead_end_vector_position[i].c[j]-1].c[deep];
                                spathl++;
                                deep--;
                                
                        ::  else ->
                                pathp--;
                                pathl++;
                                path[pathp] = dead_ends_paths[dead_end_vector_position[i].c[j]-1].c[deep];
                                spathl++;
                                break;
                        od
                ::  else -> skip;
                fi

                if
                ::  i-1>=0 && CM[i-1].c[j]==0 ->
                        i--;
                        de_preppend[prep]=0;
                        prep++;
                        spathl = spathl+2;
                        pathp--;
                        pathl++;
                        path[pathp]=1;

                ::  i+1<lines && CM[i+1].c[j]==0 ->
                        i++;
                        de_preppend[prep]=1;
                        prep++;
                        spathl = spathl+2;
                        pathp--;
                        pathl++;
                        path[pathp]=0;

                ::  j-1>=0 && CM[i].c[j-1]==0 ->
                        j--;
                        de_preppend[prep]=2;
                        prep++;
                        spathl = spathl+2;
                        pathp--;
                        pathl++;
                        path[pathp]=3;

                ::  else ->
                        j++;
                        de_preppend[prep]=3;
                        prep++;
                        spathl = spathl+2;
                        pathp--;
                        pathl++;
                        path[pathp]=2;
                fi
        ::  else ->
                ACM[i].c[j]--;
                startLine=i;
                startColumn=j;
                for(it : 0 .. pathl-1) {
                    de_append[it]=path[it+pathp];
                }
                de_append[it]=4; //mark end
                de_preppend[prep]=4;
                sc = spathl/2;
                break;
        fi
    od
    jch!_pid;
}

proctype walker(chan jch)
{
    pid threads[4];
    chan ljch = [4] of { pid };
    byte boolc;
    bool bools[4], joinable[4];

    byte it, i, j;

    ic[_pid].ready==1;
    if //BnB upper bound
    ::  (solutionSize!=0 && ic[_pid].pathSize>=solutionSize) || solutionSize==open_cells -> goto end; //return
    ::  else -> skip;
    fi

    if
    ::  ic[_pid].reg[ic[_pid].line].c[ic[_pid].column]!=5 -> ic[_pid].reg[ic[_pid].line].c[ic[_pid].column]++;
    ::  else -> ic[_pid].reg[ic[_pid].line].c[ic[_pid].column]=0;
    fi
    
    if
    ::  ic[_pid].direction!=4 -> 
            ic[_pid].path[ic[_pid].pathSize]=ic[_pid].direction;
            ic[_pid].pathSize++;
    ::  else -> skip;
    fi

    if //append dead_ends
    ::  dead_end_vector_position[ic[_pid].line].c[ic[_pid].column]!=0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column]==1 && ic[_pid].pathSize!=de_preppendSize ->
            it=0;
            do
            ::  dead_ends_paths[dead_end_vector_position[ic[_pid].line].c[ic[_pid].column]-1].c[it] != 4 ->
                    ic[_pid].path[ic[_pid].pathSize] = dead_ends_paths[dead_end_vector_position[ic[_pid].line].c[ic[_pid].column]-1].c[it];
                    ic[_pid].pathSize++;
                    it++;
            ::  else -> break;
            od
            ic[_pid].cells=ic[_pid].cells+it/2;
    ::  else -> skip;
    fi

    if //caminho completo
    ::  ic[_pid].cells==open_cells && ic[_pid].line==startLine && ic[_pid].column==startColumn ->
            atomic
            {
                m_dep==0;
                m_dep=1;
            }
            if  //false positive
            ::  solutionSize!=0 && ic[_pid].pathSize>=solutionSize ->
                    m_dep=0;
                    goto end;
            ::  else -> skip;
            fi
            it=0;
            do
            ::  scide==2 && de_append[it]!=4 ->
                    ic[_pid].path[ic[_pid].pathSize]=de_append[it];
                    it++;
                    ic[_pid].pathSize++;
            ::  else -> break;
            od
            it=0;
            do
            ::  it<ic[_pid].pathSize ->
                    solution[it]=ic[_pid].path[it]; 
                    it++;                   
            ::  else -> break;
            od
            solutionSize=ic[_pid].pathSize;
            m_dep=0;
            goto end;
    ::  else -> skip;
    fi
    
    bools[0]=ic[_pid].line-1>=0 && CM[ic[_pid].line-1].c[ic[_pid].column]==0 && ic[_pid].reg[ic[_pid].line-1].c[ic[_pid].column]==0;
    bools[1]=ic[_pid].line+1<lines && CM[ic[_pid].line+1].c[ic[_pid].column]==0 && ic[_pid].reg[ic[_pid].line+1].c[ic[_pid].column]==0;
    bools[2]=ic[_pid].column-1>=0 && CM[ic[_pid].line].c[ic[_pid].column-1]==0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column-1]==0;
    bools[3]=ic[_pid].column+1<columns && CM[ic[_pid].line].c[ic[_pid].column+1]==0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column+1]==0;
    boolc=bools[0]+bools[1]+bools[2]+bools[3]; //gives preference to never visited cells

    //calcular adjacencia
    byte adj=(ic[_pid].line-1>=0 && ic[_pid].reg[ic[_pid].line-1].c[ic[_pid].column]==0)+(ic[_pid].line+1<lines && ic[_pid].reg[ic[_pid].line+1].c[ic[_pid].column]==0)+(ic[_pid].column-1>=0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column-1]==0)+(ic[_pid].column+1>columns && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column+1]==0);
    if
    ::  ic[_pid].reg[ic[_pid].line].c[ic[_pid].column]==1 && adj==0 ->//if it is the first time a cell is being visited, it has the right to return in the opposite direction
            ic[_pid].direction=4;
    ::  else -> skip;
    fi

    if
    ::  ic[_pid].line-1>=0 && CM[ic[_pid].line-1].c[ic[_pid].column]==0 && ic[_pid].reg[ic[_pid].line-1].c[ic[_pid].column]<ACM[ic[_pid].line-1].c[ic[_pid].column] && ic[_pid].direction!=1 && (boolc==0||bools[0]) ->
            threads[0] = run walker(ljch);
            ic[threads[0]].line=ic[_pid].line-1;
            ic[threads[0]].column=ic[_pid].column;
            ic[threads[0]].direction=0;
            ic[threads[0]].cells=ic[_pid].cells+(ic[_pid].reg[ic[_pid].line-1].c[ic[_pid].column]==0 -> 1:0);
            i=0;
            do
            ::  i<ic[_pid].pathSize ->
                    ic[threads[0]].path[i]=ic[_pid].path[i];
                    i++;
            ::  else -> break;
            od
            ic[threads[0]].pathSize=i;
            i=0;
            do
            ::  i<lines ->
                    j=0;
                    do
                    ::  j<columns ->
                            ic[threads[0]].reg[i].c[j]=ic[_pid].reg[i].c[j];
                            j++;
                    ::  else -> break;
                    od
                    i++;
            ::  else -> break;
            od
            ic[threads[0]].ready=1;
            joinable[0]=1;
    ::  else -> skip;
    fi

    if
    ::  ic[_pid].line+1<lines && CM[ic[_pid].line+1].c[ic[_pid].column]==0 && ic[_pid].reg[ic[_pid].line+1].c[ic[_pid].column]<ACM[ic[_pid].line+1].c[ic[_pid].column] && ic[_pid].direction!=0 && (boolc==0||bools[1]) ->
            threads[1] = run walker(ljch);
            ic[threads[1]].line=ic[_pid].line+1;
            ic[threads[1]].column=ic[_pid].column;
            ic[threads[1]].direction=1;
            ic[threads[1]].cells=ic[_pid].cells+(ic[_pid].reg[ic[_pid].line+1].c[ic[_pid].column]==0 -> 1:0);
            i=0;
            do
            ::  i<ic[_pid].pathSize ->
                    ic[threads[1]].path[i]=ic[_pid].path[i];
                    i++;
            ::  else -> break;
            od
            ic[threads[1]].pathSize=i;
            i=0;
            do
            ::  i<lines ->
                    j=0;
                    do
                    ::  j<columns ->
                            ic[threads[1]].reg[i].c[j]=ic[_pid].reg[i].c[j];
                            j++;
                    ::  else -> break;
                    od
                    i++;
            ::  else -> break;
            od
            ic[threads[1]].ready=1;
            joinable[1]=1;
    ::  else -> skip;
    fi

    if
    ::  ic[_pid].column-1>=0 && CM[ic[_pid].line].c[ic[_pid].column-1]==0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column-1]<ACM[ic[_pid].line].c[ic[_pid].column-1] && ic[_pid].direction!=3 && (boolc==0||bools[2]) ->
            threads[2] = run walker(ljch);
            ic[threads[2]].line=ic[_pid].line;
            ic[threads[2]].column=ic[_pid].column-1;
            ic[threads[2]].direction=2;
            ic[threads[2]].cells=ic[_pid].cells+(ic[_pid].reg[ic[_pid].line].c[ic[_pid].column-1]==0 -> 1:0);
            i=0;
            do
            ::  i<ic[_pid].pathSize ->
                    ic[threads[2]].path[i]=ic[_pid].path[i];
                    i++;
            ::  else -> break;
            od
            ic[threads[2]].pathSize=i;
            i=0;
            do
            ::  i<lines ->
                    j=0;
                    do
                    ::  j<columns ->
                            ic[threads[2]].reg[i].c[j]=ic[_pid].reg[i].c[j];
                            j++;
                    ::  else -> break;
                    od
                    i++;
            ::  else -> break;
            od
            ic[threads[2]].ready=1;
            joinable[2]=1;
    ::  else -> skip;
    fi

    if
    ::  ic[_pid].column+1<columns && CM[ic[_pid].line].c[ic[_pid].column+1]==0 && ic[_pid].reg[ic[_pid].line].c[ic[_pid].column+1]<ACM[ic[_pid].line].c[ic[_pid].column+1] && ic[_pid].direction!=2 && (boolc==0||bools[3]) ->
            threads[3] = run walker(ljch);
            ic[threads[3]].line=ic[_pid].line;
            ic[threads[3]].column=ic[_pid].column+1;
            ic[threads[3]].direction=3;
            ic[threads[3]].cells=ic[_pid].cells+(ic[_pid].reg[ic[_pid].line].c[ic[_pid].column+1]==0 -> 1:0);
            i=0;
            do
            ::  i<ic[_pid].pathSize ->
                    ic[threads[3]].path[i]=ic[_pid].path[i];
                    i++;
            ::  else -> break;
            od
            ic[threads[3]].pathSize=i;
            i=0;
            do
            ::  i<lines ->
                    j=0;
                    do
                    ::  j<columns ->
                            ic[threads[3]].reg[i].c[j]=ic[_pid].reg[i].c[j];
                            j++;
                    ::  else -> break;
                    od
                    i++;
            ::  else -> break;
            od
            ic[threads[3]].ready=1;
            joinable[3]=1;
    ::  else -> skip;
    fi

    for(it : 0 .. 3){
        if
        ::  joinable[it] -> ljch??threads[it];
        ::  else -> skip;
        fi
    }

    end:
    jch!_pid;
}

init
{
    byte i, j, dep; //dep: dead_ends position
    chan jch =[255] of { pid };
    pid pids[255]; 

    coords dead_ends[255];

    STDIN?startLine,_,startColumn,_;
    startLine=startLine-48;
    startColumn=startColumn-48;

    for(i : 0 .. lines-1) {
        for(j : 0 .. columns-1) {
            STDIN?CM[i].c[j];
            CM[i].c[j]=CM[i].c[j]-48;
        }
        STDIN?_; // requires a new line at the ed of the matrix
    }

    //ACM initialization
    ACM[0].c[0] = (CM[0].c[0]==0 -> (CM[1].c[0]==0 -> 1:0)+(CM[0].c[1]==0 -> 1:0) : 0);
    ACM[lines-1].c[0] = (CM[lines-1].c[0]==0 -> (CM[lines-2].c[0]==0 -> 1:0)+(CM[lines-1].c[1]==0 -> 1:0) : 0);
    ACM[0].c[columns-1] = (CM[0].c[columns-1]==0 -> (CM[1].c[columns-1]==0 -> 1:0)+(CM[0].c[columns-2]==0 -> 1:0) : 0);
    ACM[lines-1].c[columns-1] = (CM[lines-1].c[columns-1]==0 -> (CM[lines-2].c[columns-1]==0 -> 1:0)+(CM[lines-1].c[columns-2]==0 -> 1:0) : 0);

    i=0;
    for(j : 1 .. columns-2) {
        ACM[i].c[j] = (CM[i].c[j]==0 -> ((CM[i+1].c[j]==0 -> 1:0)+(CM[i].c[j+1]==0 -> 1:0)+(CM[i].c[j-1]==0 -> 1:0)) : 0);
    }
    i=lines-1;
    for(j : 1 .. columns-2) {
        ACM[i].c[j] = (CM[i].c[j]==0 -> ((CM[i-1].c[j]==0 -> 1:0)+(CM[i].c[j+1]==0 -> 1:0)+(CM[i].c[j-1]==0 -> 1:0)) : 0);
    }
    j=0;
    for(i : 1 .. lines-2) {
        ACM[i].c[j] = (CM[i].c[j]==0 -> ((CM[i+1].c[j]==0 -> 1:0)+(CM[i-1].c[j]==0 -> 1:0)+(CM[i].c[j+1]==0 -> 1:0)) : 0);        
    }
    j=columns-1;
    for(i : 1 .. lines-2) {
        ACM[i].c[j] = (CM[i].c[j]==0 -> ((CM[i+1].c[j]==0 -> 1:0)+(CM[i-1].c[j]==0 -> 1:0)+(CM[i].c[j-1]==0 -> 1:0)) : 0);        
    }
    for(i : 1 .. lines-2) {
        for(j : 1 .. columns-2) {
            ACM[i].c[j] = (CM[i].c[j]==0 -> ((CM[i+1].c[j]==0 -> 1:0)+(CM[i-1].c[j]==0 -> 1:0)+(CM[i].c[j+1]==0 -> 1:0)+(CM[i].c[j-1]==0 -> 1:0)) : 0);
        }
    }

    //dead_ends find and open_cells count
    for(i : 0 .. lines-1) {
        for(j : 0 .. columns-1) {
            if
            ::  ACM[i].c[j]==1 -> 
                    dead_ends[dep].line=i;
                    dead_ends[dep].column=j;
                    dep++;
            ::  else -> skip;
            fi
            if
            ::  ACM[i].c[j]!=0 -> open_cells++;
            ::  else -> skip;
            fi
        }
    }

    //dead_ends
    for(i : 0 .. dep-1) {
        pids[i] = run dead_end_thread(dead_ends[i].line, dead_ends[i].column, jch);
    }
    for(i : 0 .. dep-1) { //join
        jch??eval(pids[i]);
    }
    if
    ::  scide == 2 ->
            pids[0] = run dead_end_sc(startLine, startColumn, jch);
            jch??eval(pids[0]);
    ::  else -> skip;
    fi

    //ACM reduction
    byte t;
    for(i : 1 .. lines-1){
        for(j : 1 .. columns-1){
            if
            ::  ACM[i].c[j]==4 ->
                    t=0;
                    if
                    ::  CM[i+1].c[j+1]==1 -> t++;
                    ::  else-> skip;
                    fi
                    if
                    ::  CM[i+1].c[j-1]==1 -> t++;
                    ::  else-> skip;
                    fi
                    if
                    ::  CM[i-1].c[j+1]==1 -> t++;
                    ::  else-> skip;
                    fi
                    if
                    ::  CM[i-1].c[j-1]==1 -> t++;
                    ::  else-> skip;
                    fi
                    if
                    ::  t==0 -> ACM[i].c[j]=2;
                    ::  else-> skip;
                    fi
            :: else -> skip;
            fi
        }
    }
    
    //walker
    pid cp;
    cp = run walker(jch);
    ic[cp].line=startLine;
    ic[cp].column=startColumn;
    ic[cp].direction=4//no direction
    ic[cp].cells=sc;
    i=0;
    do
    ::  scide==2 && de_preppend[i]!=4 ->
            ic[cp].path[i]=de_preppend[i];
            i++;
    ::  else -> break;
    od
    if
    ::  scide!=2 -> 
        ic[cp].pathSize=0;
        de_preppendSize=0;
    ::  else ->
        ic[cp].pathSize=i;
        de_preppendSize=i;
    fi
    ic[cp].reg[startLine].c[startColumn]=5; //5 replaces -1;
    ic[cp].ready=1;
    jch??eval(cp);

    byte it;
    do
    ::  it<solutionSize -> printf("%d", solution[it]); it++;
    ::  else -> printf("\n"); break;
    od
}