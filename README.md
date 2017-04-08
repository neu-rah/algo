# Algo - Algebra Objects

Computer Algebra Experiments

## includes:
**Rules system** - transform algebra expressions by transformation description also in algebra expression
  (programmable calculation with algebra language)

**parser** - text parser for algebra expressions (quite rough)

**calc** - numerical calculation and some obvious operations like neutral removal

**simplify** - apply internal simplification rules

**evid** - try to isolate a sub-expression

**solve** - draw solving steps

**verify** - verifies the result (not for simple numeric calc)

## samples
    R=E/I ⇔ I=E/R

    a=x ∧ a=1 ⇔ 1=x ∧ a=1 ⇔ x=1 ∧ a=1

    a ∈ [0;1[ ∧ a+b=12 ⇔ a≥0 ∧ a<1 ∧ b≤12 ∧ b>11

    ]-∞;2] ∩ ]2;10[=∅

    a-a²=0 ⇔ a=(-1±root((1-0),2))/-2 ⇔ a=(-1±root((1+0),2))/-2 ⇔ a=(-1±root(1,2))/-2 ⇔ a=(-1±1)/-2 ⇔ a=(0 ∨ -1-1)/-2 ⇔ a=(0 ∨ -2)/-2 ⇔ a=-0/2 ∨ 2/2 ⇔ a=-0 ∨ 1 ⇔ a=0 ∨ 1 ⇔ a=0 ∨ a=1

    5.0V/50.0mA=100.0Ω

    |f(x)=2·x ⇔ |f(x)=2·x ⇔ |f(x)=2·x ⇔ |f(x)=2·x
    |f(y)=98    |2·y=98     |y=98/2     |y=49


    |f(n)=2·n   ⇔ |n·2=2·n ⇔ |True ⇔ True
    |f⁻¹(x)=x/2   |x/2=x/2   |True
