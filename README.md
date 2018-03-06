# DataFlowPointerAnalysis

Analyze function pointer by using data flow equation based on LLVM/Clang.

x=&y;                S’ = S ⁄ {x →S(x)} ∪ {x →y} 

x=y;                 S’ = S ⁄ {x →S(x)} ∪ {x →S(y)}

x=*y;                S’ = S ⁄ {x →S(x)} ∪ {x →S(S(y))}
          OR         S ⁄ {v →S(v)} ∪ {v →S(y)}             (S(x)={v})
          
*x=y;                S ∪ {v0 →S(y)} …∪ {vn →S(y)}    (S(x)={v0…vn})
          OR         ⊤                                              (S(x)={}) 
