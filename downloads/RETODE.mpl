

# Loading necessary packages

read("qsum19.mpl");
read("hsum19.mpl");


###############################################################################

REtoqHahn:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aH, bH, NH, M, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill,
q_exp1, q_exp2, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars, qeq, NHsol, new_eqs,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = M^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), M);
Bdenom := collect(expand(denom(tillB)), M);
Cnumer := collect(expand(numer(tillC)), M);
Cdenom := collect(expand(denom(tillC)), M);

if degree(Bnumer, M) > 6 or degree(Bdenom, M) > 6 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -((M*(M^2*aH^2*bH^2*q^(NH+2)+M^2*aH^2*bH*q^(NH+2)-M*aH^2*bH*q^(NH+2)-M*aH*bH*q^(NH+2)-M*aH^2*bH*q^(NH+1)-M*aH*bH*q^(NH+1)+aH*bH*q^(NH+1)+aH*q^(NH+1)+M^2*aH^2*bH*q+M^2*aH*bH*q-M*aH*bH*q-M*aH*q-M*aH*bH-M*aH+aH+1))/((M^2*aH*bH-1)*q^NH*(M^2*aH*bH*q^2-1))); 
Ctill := -M*q^(-2*NH)*(M-1)*(M-q^(1+NH))*aH*(M*aH-1)*(M*bH-1)*(M*aH*bH-1)*(aH*bH*M*q^(1+NH)-1)/((M^2*aH*bH-1)^2*(M^2*aH*bH-q)*(M^2*aH*bH*q-1));

q_exp1 := proc(expr) return applyrule(q^(NH*n::integer + r::anything) = u^n*q^r, expr); end proc;
q_exp2 := proc(expr) return applyrule(q^(N*n::integer + r::anything) = v^n*q^r, expr); end proc;

Btill := q_exp1(Btill);
Ctill := q_exp1(Ctill);

Btillnumer := collect(expand(numer(Btill)), M);
Btilldenom := collect(expand(denom(Btill)), M);
Ctillnumer := collect(expand(numer(Ctill)), M);
Ctilldenom := collect(expand(denom(Ctill)), M);

Bnumer := q_exp2(Bnumer);
Cnumer := q_exp2(Cnumer);
Bdenom := q_exp2(Bdenom);
Cdenom := q_exp2(Cdenom);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), M);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), M);

Sol := {coeffs(eqB, M)}; 
Sol := {coeffs(eqC, M), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aH, bH, f, g, u}, explicit)};

solutions := subs([u = q^NH, v = q^N], solutions);

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as q-Hahn or a linear transformation";
end if;

parameters := remove(x -> member(x, {NH, aH, bH, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   # Solving for NH
   qeq := select(has, sol, q^NH); 
   NHsol := solve(qeq[1], NH); 
   new_eqs := remove(has, sol, q^NH); 
   sol := [op(new_eqs), NH = NHsol];

   sigmax := factor(subs(sol, subs(x = f*x+g, -q^(-NH-1)*(q^NH*x-1)*(aH*q-x)*f^2))); 
   taux := factor(subs(sol, subs(x = f*x+g, q^(-NH-1)*(q^(NH+2)*x*aH*bH-q^(NH+2)*aH*bH+q^(NH+1)*aH-q*aH-q^NH*x+1)*f/(q-1)))); 
   lambdan := factor(subs(sol, subs(x = f*x+g, -(q^n-1)*(q^(n+1)*aH*bH-1)/((q-1)^2*q^n)))); 
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)];
   elif is(subs(sol, f) < 0) then 
      interval := [subs(sol, (-g+NH)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", solutions);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      
      # Solving for NH
      qeq := select(has, sol, q^NH); 
      NHsol := solve(qeq[1], NH); 
      new_eqs := remove(has, sol, q^NH); 
      sol := [op(new_eqs), NH = NHsol]; 

      sigmax := factor(subs(sol, subs(x = f*x+g, -q^(-NH-1)*(q^NH*x-1)*(aH*q-x)*f^2))); 
      taux := factor(subs(sol, subs(x = f*x+g, q^(-NH-1)*(q^(NH+2)*x*aH*bH-q^(NH+2)*aH*bH+q^(NH+1)*aH-q*aH-q^NH*x+1)*f/(q-1)))); 
      lambdan := factor(subs(sol, subs(x = f*x+g, -(q^n-1)*(q^(n+1)*aH*bH-1)/((q-1)^2*q^n)))); 
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)];
      elif is(subs(sol, f) < 0) then 
         interval := [subs(sol, (-g+NH)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:








REtoBigJ:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aB, bB, cB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, j, interval:=[cB*q,aB*q], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, N) > 4 or degree(Bdenom, N) > 4 or degree(Cnumer, N) > 7 or degree(Cdenom, N) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -N*q*(N^2*aB^2*bB^2*q+N^2*aB^2*bB*cB*q+N^2*aB^2*bB*q+N^2*aB*bB*cB*q-N*aB^2*bB*q-N*aB*bB*cB*q-N*aB^2*bB-N*aB*bB*cB-N*aB*bB*q-N*aB*cB*q-N*aB*bB-N*aB*cB+aB*bB+aB*cB+aB+cB)/((N^2*aB*bB-1)*(N^2*aB*bB*q^2-1));
Ctill := -(N-1)*N*aB*(N*aB-1)*(N*bB-1)*(N*aB*bB-1)*(-N*aB*bB+cB)*(N*cB-1)*q^2/((N^2*aB*bB-1)^2*(-N^2*aB*bB+q)*(N^2*aB*bB*q-1));

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, bB, cB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Big q-Jacobi or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, bB, cB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x+g, (-aB*q+x)*(-cB*q+x)*f^2/q)));
   taux := factor(subs(sol, subs(x = f*x+g, (aB*bB*q^2*x-aB*bB*q^2-aB*cB*q^2+aB*q+cB*q-x)*f/((q-1)*q))));
   lambdan := factor(subs(sol, subs(x = f*x+g, -(q^n-1)*(aB*bB*q^(n+1)-1)/((q-1)^2*q^n))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = P[n](subs(sol, aB), subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = P[n](subs(sol, aB), subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f*x+g, (-aB*q+x)*(-cB*q+x)*f^2/q)));
      taux := factor(subs(sol, subs(x = f*x+g, (aB*bB*q^2*x-aB*bB*q^2-aB*cB*q^2+aB*q+cB*q-x)*f/((q-1)*q))));
      lambdan := factor(subs(sol, subs(x = f*x+g, -(q^n-1)*(aB*bB*q^(n+1)-1)/((q-1)^2*q^n))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = P[n](subs(sol, aB), subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = intervallist];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:






REtoLilJ:= proc(RE, pn, x, q)
local P, n, re, ord, Pnplus1, tn, An, Bn, Cn, A, q_expansion, aB, bB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

P := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, P(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
Pnplus1 := expand((-coeff(re, P(n))*P(n)-coeff(re, P(n-1))*P(n-1))/coeff(re, P(n+1)));
if degree(Pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(Pnplus1, P(n)), x); 
Cn := -collect(coeff(Pnplus1, P(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, M) > 4 or degree(Bdenom, M) > 4 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -N*(N^2*aB^2*bB*q+N^2*aB*bB*q-N*aB*bB*q-N*aB*bB-N*aB*q-N*aB+aB+1)/((N^2*aB*bB-1)*(N^2*aB*bB*q^2-1)); 
Ctill := (N-1)*N^2*aB*(N*aB-1)*(N*bB-1)*(N*aB*bB-1)/((N^2*aB*bB-1)^2*(N^2*aB*bB-q)*(N^2*aB*bB*q-1));

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, bB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Little q-Jacobi or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, bB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x + g, ((x - 1)*x/q)*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, ((aB*bB*q^2*x - x - aB*q + 1)/((q - 1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, -((1 - q^n)*(1 - aB*bB*q^(n + 1)))/((q - 1)^2*q^n))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = p[n](subs(sol, aB), subs(sol, bB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = p[n](subs(sol, aB), subs(sol, bB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 

      sigmax := factor(subs(sol, subs(x = f*x + g, ((x - 1)*x/q)*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, ((aB*bB*q^2*x - x - aB*q + 1)/((q - 1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, -((1 - q^n)*(1 - aB*bB*q^(n + 1)))/((q - 1)^2*q^n)))); 
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = p[n](subs(sol, aB), subs(sol, bB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:





REtoqL:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aL, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
q_exp1, q_exp2, qeq, aLsol, new_eqs, Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, j, interval:=[0, infinity], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, N) > 4 or degree(Bdenom, N) > 4 or degree(Cnumer, N) > 7 or degree(Cdenom, N) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (q^(-aL-1)*(N*q^(aL+1)+N*q-q-1))/N^2;
Ctill := ((N-1)*q^(1-2*aL)*(N*q^aL-1))/N^4;

q_exp1 := proc(expr) return applyrule(q^(aL*n::integer + r::anything) = u^n*q^r, expr); end proc;
q_exp2 := proc(expr) return applyrule(q^(a*n::integer + r::anything) = v^n*q^r, expr); end proc;

Btill := q_exp1(Btill);
Ctill := q_exp1(Ctill);

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

Bnumer := q_exp2(Bnumer);
Cnumer := q_exp2(Cnumer);
Bdenom := q_exp2(Bdenom);
Cdenom := q_exp2(Cdenom);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {u, f, g}, explicit)};

solutions := subs([u = q^aL, v = q^a], solutions);

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as q-Laguerre or a linear transformation";
end if;

parameters := remove(x -> member(x, {aL, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   # Solving for aL
   qeq := select(has, sol, q^aL); 
   aLsol := solve(qeq[1], aL); 
   new_eqs := remove(has, sol, q^aL); 
   sol := [op(new_eqs), aL = aLsol];

   sigmax := factor(subs(sol, subs(x = f*x + g, (x/q)*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, ((q^(aL + 1)*x + q^(aL + 1) - 1)/((q - 1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, (q^aL*(1 - q^n))/((q - 1)^2))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) =  L[n](subs(sol, aL), subs(sol, subs(x = f * x + g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", solutions);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) =  L[n](subs(sol, aL), subs(sol, subs(x = f * x + g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      # Solving for aL
      qeq := select(has, sol, q^aL); 
      aLsol := solve(qeq[1], aL); 
      new_eqs := remove(has, sol, q^aL); 
      sol := [op(new_eqs), aL = aLsol];

      sigmax := factor(subs(sol, subs(x = f*x + g, (x/q)*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, ((q^(aL + 1)*x + q^(aL + 1) - 1)/((q - 1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, (q^aL*(1 - q^n))/((q - 1)^2))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) =  L[n](subs(sol, aL), subs(sol, subs(x = f * x + g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = intervallist];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:




REtoqB:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, M) > 4 or degree(Bdenom, M) > 4 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (N*(N^2*aB*q - N*aB*q - q - N*aB)) / ((q + N^2*aB)*(N^2*aB*q + 1));
Ctill := -((N - 1)*N^3*aB*q*(q + N*aB)) / ((N^2*aB + 1)*(q + N^2*aB)^2*(q^2 + N^2*aB));

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as q-Bessel or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);
   
   sigmax := factor(subs(sol, subs(x = f*x + g, ((1 - x)*x/q)*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, ((aB*q*x + x - 1)/((q - 1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, -((1 - q^n)*(aB*q^n + 1))/((q - 1)^2*q^n))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
  
      sigmax := factor(subs(sol, subs(x = f*x + g, ((1 - x)*x/q)*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, ((aB*q*x + x - 1)/((q - 1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, -((1 - q^n)*(aB*q^n + 1))/((q - 1)^2*q^n))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:




REtoAS1:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, j, interval:=[aB, 1], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, N) > 4 or degree(Bdenom, N) > 4 or degree(Cnumer, N) > 7 or degree(Cdenom, N) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -(N*(aB+1));
Ctill := ((N-1)*N*aB)/q;

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Al-Salam Carlitz I or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);
   
   sigmax := factor(subs(sol, subs(x = f*x + g, ((1 - x)*(aB - x)/q)*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, -((x - aB - 1)/((q - 1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, (q^n - 1)/((q - 1)^2*q^n))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = U[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = U[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];
   
      sigmax := factor(subs(sol, subs(x = f*x + g, ((1 - x)*(aB - x)/q)*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, -((x - aB - 1)/((q - 1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, (q^n - 1)/((q - 1)^2*q^n))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = U[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = intervallist];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:



REtoAS2:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, aB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, M) > 4 or degree(Bdenom, M) > 4 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -((aB+1)/N):
Ctill := -(((N-1)*aB*q)/N^2);

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Al-Salam Carlitz II or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);
   
   sigmax := factor(subs(sol, subs(x = f * x + g, (aB)*f^2)));
   taux := factor(subs(sol, subs(x = f * x + g, ((x-aB-1)/(q-1))*f)));
   lambdan := factor(subs(sol, subs(x = f * x + g, (-((q^n-1)/(q-1)^2)))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = V[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = V[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
  
      sigmax := factor(subs(sol, subs(x = f * x + g, (aB)*f^2)));
      taux := factor(subs(sol, subs(x = f * x + g, ((x-aB-1)/(q-1))*f)));
      lambdan := factor(subs(sol, subs(x = f * x + g, (-((q^n-1)/(q-1)^2)))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = V[n](subs(sol, aB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:



REtoqM:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, bB, cB, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, M) > 4 or degree(Bdenom, M) > 4 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (N*bB*cB*q + N*cB*q - cB*q - N*q - cB) / (N^2*q);
Ctill := ((N - 1)*(N*bB - 1)*cB*(cB + N)*q) / N^4;

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {bB, cB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as q-Meixner or a linear transformation";
end if;

parameters := remove(x -> member(x, {bB, cB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);
   
   sigmax := factor(subs(sol, subs(x = f*x + g, (cB*(x - bB*q)/q)*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, ((q*x + bB*cB*q - q - cB)/((q - 1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, -((q^n - 1)/((q - 1)^2)))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
  
      sigmax := factor(subs(sol, subs(x = f*x + g, (cB*(x - bB*q)/q)*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, ((q*x + bB*cB*q - q - cB)/((q - 1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, -((q^n - 1)/((q - 1)^2)))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bB), subs(sol, cB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:




REtoqK:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, pB, NB, M, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill,
q_exp1, q_exp2, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars, qeq, NBsol, new_eqs,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = M^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), M);
Bdenom := collect(expand(denom(tillB)), M);
Cnumer := collect(expand(numer(tillC)), M);
Cdenom := collect(expand(denom(tillC)), M);

if degree(Bnumer, M) > 4 or degree(Bdenom, M) > 4 or degree(Cnumer, M) > 7 or degree(Cdenom, M) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -((M*(M*pB*q^(NB + 2) + M^2*pB^2*q^(NB + 1) + M*pB*q^(NB + 1) - pB*q^(NB + 1) - M^2*pB*q + M*pB*q + q + M*pB)) / (q^NB*(q + M^2*pB)*(M^2*pB*q + 1)));
Ctill := -(((M - 1)*M^2*pB*q^(1 - 2*NB)*(q + M*pB)*(M*pB*q^NB + 1)*(M - q^(NB + 1))) / ((M^2*pB + 1)*(q + M^2*pB)^2*(q^2 + M^2*pB)));


q_exp1 := proc(expr) return applyrule(q^(NB*n::integer + r::anything) = u^n*q^r, expr); end proc;
q_exp2 := proc(expr) return applyrule(q^(N*n::integer + r::anything) = v^n*q^r, expr); end proc;

Btill := q_exp1(Btill);
Ctill := q_exp1(Ctill);

Btillnumer := collect(expand(numer(Btill)), M);
Btilldenom := collect(expand(denom(Btill)), M);
Ctillnumer := collect(expand(numer(Ctill)), M);
Ctilldenom := collect(expand(denom(Ctill)), M);

Bnumer := q_exp2(Bnumer);
Cnumer := q_exp2(Cnumer);
Bdenom := q_exp2(Bdenom);
Cdenom := q_exp2(Cdenom);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), M);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), M);

Sol := {coeffs(eqB, M)}; 
Sol := {coeffs(eqC, M), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {pB, f, g, u}, explicit)};

solutions := subs([u = q^NB, v = q^N], solutions);

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as q-Krawtchouk or a linear transformation";
end if;

parameters := remove(x -> member(x, {NB, pB, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   # Solving for NB
   qeq := select(has, sol, q^NB); 
   NBsol := solve(qeq[1], NB); 
   new_eqs := remove(has, sol, q^NB); 
   sol := [op(new_eqs), NB = NBsol];
   
   sigmax := factor(subs(sol, subs(x = f*x + g, (q^(-NB - 1)*x*(q^NB*x - 1))*f^2)));
   taux := factor(subs(sol, subs(x = f*x + g, -((q^(-NB - 1)*(pB*q^(NB + 1)*x + q^NB*x - pB*q^(NB + 1) - 1)) / (q - 1))*f)));
   lambdan := factor(subs(sol, subs(x = f*x + g, ((q^n - 1)*(pB*q^n + 1)) / ((q - 1)^2*q^n))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NB)/f)]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NB)/f)];
   elif is(subs(sol, f) < 0) then 
      interval := [subs(sol, (-g+NB)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pB), subs(sol, NB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", solutions);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pB), subs(sol, NB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      
      # Solving for NB
      qeq := select(has, sol, q^NB); 
      NBsol := solve(qeq[1], NB); 
      new_eqs := remove(has, sol, q^NB); 
      sol := [op(new_eqs), NB = NBsol]; 

      sigmax := factor(subs(sol, subs(x = f*x + g, (q^(-NB - 1)*x*(q^NB*x - 1))*f^2)));
      taux := factor(subs(sol, subs(x = f*x + g, -((q^(-NB - 1)*(pB*q^(NB + 1)*x + q^NB*x - pB*q^(NB + 1) - 1)) / (q - 1))*f)));
      lambdan := factor(subs(sol, subs(x = f*x + g, ((q^n - 1)*(pB*q^n + 1)) / ((q - 1)^2*q^n)))); 
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NB)/f)]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NB)/f)];
      elif is(subs(sol, f) < 0) then 
         interval := [subs(sol, (-g+NB)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pB), subs(sol, NB), subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:





REtoSW:= proc(RE, pn, x, q)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, q_expansion, N, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, j, interval:=[0, infinity], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

q_expansion := proc(expr) return applyrule(q^(n*m::integer + r::anything) = N^m*q^r, expr); end proc;

tillB := factor(normal(q_expansion(Bn/An)));
tillC := factor(normal(q_expansion(Cn/(An*subs(n = n - 1, An)))));

Bnumer := collect(expand(numer(tillB)), N);
Bdenom := collect(expand(denom(tillB)), N);
Cnumer := collect(expand(numer(tillC)), N);
Cdenom := collect(expand(denom(tillC)), N);

if degree(Bnumer, N) > 4 or degree(Bdenom, N) > 4 or degree(Cnumer, N) > 7 or degree(Cdenom, N) > 8 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (N*q-q-1)/(N^2*q);
Ctill := -(((N-1)*q)/N^4);

Btillnumer := collect(expand(numer(Btill)), N);
Btilldenom := collect(expand(denom(Btill)), N);
Ctillnumer := collect(expand(numer(Ctill)), N);
Ctilldenom := collect(expand(denom(Ctill)), N);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), N);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), N);

Sol := {coeffs(eqB, N)}; 
Sol := {coeffs(eqC, N), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Stieltjes-Wigert or a linear transformation";
end if;

parameters := remove(x -> member(x, {f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);
   
   sigmax := factor(subs(sol, subs(x = f * x + g, (x/q)*f^2)));
   taux := factor(subs(sol, subs(x = f * x + g, ((q*x-1)/((q-1)*q))*f)));
   lambdan := factor(subs(sol, subs(x = f * x + g, -((q^n-1)/(q-1)^2))));
   DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
   DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

   sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
   tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
   lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
   if sigmaz = 0 then sigmaz := sigmax end if; 
   if tauz = 0 then tauz := taux end if; 
   if lambdaz = 0 then lambdaz := lambdan end if; 
   
   density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = S[n](subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = S[n](subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f * x + g, (x/q)*f^2)));
      taux := factor(subs(sol, subs(x = f * x + g, ((q*x-1)/((q-1)*q))*f)));
      lambdan := factor(subs(sol, subs(x = f * x + g, -((q^n-1)/(q-1)^2))));
      DI := factor(sigmax*Dq(Dq(p(n, x), x, 1/q), x, q)) + factor(taux*Dq(p(n, x), x, q)) + factor(lambdan*p(n, x)); 
      DI := subs(Dq(Dq(p(n, x), x, 1/q), x, q) = term1, Dq(p(n, x), x, q) = term2, p(n, x) = term3, DI); 
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]); 

      sigmaz := factor(coeff(DI, term1)/((q-1)^2*q)); 
      tauz := factor(coeff(DI, term2)/((q-1)^2*q)); 
      lambdaz := factor(coeff(DI, term3)/((q-1)^2*q)); 
      if sigmaz = 0 then sigmaz := sigmax end if; 
      if tauz = 0 then tauz := taux end if; 
      if lambdaz = 0 then lambdaz := lambdan end if; 

      density := factor((sigmaz+(q-1)*x*tauz)/subs(x = q*x, sigmaz)); 
    
      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = S[n](subs(sol, subs(x = f*x+g, x)), q), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = intervallist];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:





REtoqDE := proc(RE, pn, x, q)
    local results, result, sub_funcs, f, i;
    results := [];
    
    sub_funcs := [REtoBigJ, REtoLilJ, REtoqL, REtoqB, 
                  REtoAS1, REtoAS2, REtoqM, REtoqK, REtoqHahn, REtoSW];
    
    for i from 1 to nops(sub_funcs) do
        f := sub_funcs[i];
        try
            result := f(RE, pn, x, q);
            results := [op(results), result];
        catch:
            # If an error occurs, just skip to the next one
        end try;
    end do;

    if nops(results) > 0 then
        return results;
    else
        error "No classical q-orthogonal polynomial solution found";
    end if;
end proc:



REtoqde := proc(RE, pn, x, q)
    local results, result, sub_funcs, f, func_name, func_proc, i;
    results := [];

    sub_funcs := [
        ["Has a solution as Big q-Jacobi", REtoBigJ],
        ["Has a solution as Little q-Jacobi", REtoLilJ],
        ["Has a solution as q-Laguerre", REtoqL],
        ["Has a solution as q-Bessel", REtoqB],
        ["Has a solution as Al-Salam Carlitz I", REtoAS1],
        ["Has a solution as Al-Salam Carlitz II", REtoAS2],
        ["Has a solution as q-Meixner", REtoqM],
        ["Has a solution as q-Krawtchouk", REtoqK],
        ["Has a solution as q-Hahn", REtoqHahn],
        ["Has a solution as Stieltjes-Wigert", REtoSW]
    ];

    for i from 1 to nops(sub_funcs) do
        func_name := sub_funcs[i][1];
        func_proc := sub_funcs[i][2];
        try
            result := func_proc(RE, pn, x, q);
            results := [op(results), [func_name, result]];
        catch:
            # skip on error
        end try;
    end do;

    if nops(results) > 0 then
        return results;
    else
        error "No solution found";
    end if;
end proc:



###############################################################################


REtoJacobi:= proc(RE, pn, x)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, aJ, bJ, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DE, DElist, density, parameters, f, g, i, j, interval:=[-1,1], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, N) > 2 or degree(Bdenom, N) > 2 or degree(Cnumer, N) > 4 or degree(Cdenom, N) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -(bJ-aJ)*(bJ+aJ)/((2*n+bJ+aJ)*(2*n+bJ+aJ+2));
Ctill := 4*n*(n+aJ)*(n+bJ)*(n+bJ+aJ)/((2*n+bJ+aJ-1)*(2*n+bJ+aJ)^2*(2*n+bJ+aJ+1));

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aJ, bJ, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Jacobi or a linear transformation";
end if;

parameters := remove(x -> member(x, {aJ, bJ, f, g}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x+g, (x+1)*(x-1)/f^2)));
   taux := factor(subs(sol, subs(x = f*x+g, ((aJ+bJ+2)*x+aJ-bJ)/f)));
   lambdan := factor(subs(sol, subs(x = f*x+g, -n*(n+bJ+aJ+1))));
   DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
   DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
   DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
   density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x)));

   
   sigmaz := factor(coeff(DE, term1)); 
   tauz := factor(coeff(DE, term2)); 
   lambdaz := factor(coeff(DE, term3));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;
   #interval := sort(interval, (a, b) -> evalb(a < b));

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = P[n](subs(sol, aJ), subs(sol, bJ), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = P[n](subs(sol, aJ), subs(sol, bJ), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   DElist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f*x+g, (x+1)*(x-1)/f^2)));
      taux := factor(subs(sol, subs(x = f*x+g, ((aJ+bJ+2)*x+aJ-bJ)/f)));
      lambdan := factor(subs(sol, subs(x = f*x+g, -n*(n+bJ+aJ+1))));
      DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
      DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
      DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
      density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x))); 

      
      sigmaz := factor(coeff(DE, term1)); 
      tauz := factor(coeff(DE, term2)); 
      lambdaz := factor(coeff(DE, term3));

      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;
      #intervallist := sort(intervallist, (a, b) -> evalb(a < b));

      DElist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = P[n](subs(sol, aJ), subs(sol, bJ), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(DElist) > 1 then
   print("Warning, several solutions found");
   return(DElist);
end if;

end proc:




REtoLaguerre:= proc(RE, pn, x)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, aL, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DE, DElist, density, parameters, f, g, i, j, interval:=[0, infinity], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, N) > 2 or degree(Bdenom, N) > 2 or degree(Cnumer, N) > 4 or degree(Cdenom, N) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -2*n-aL-1;
Ctill := n*(n+aL);

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aL, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Laguerre or a linear transformation";
end if;

parameters := remove(x -> member(x, {aL, f, g}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x+g, x/f^2)));
   taux := factor(subs(sol, subs(x = f*x+g, (-x + aL + 1)/f)));
   lambdan := factor(subs(sol, subs(x = f*x+g, n)));
   DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
   DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
   DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
   density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x)));

   
   sigmaz := factor(coeff(DE, term1)); 
   tauz := factor(coeff(DE, term2)); 
   lambdaz := factor(coeff(DE, term3));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;
   #interval := sort(interval, (a, b) -> evalb(a < b));

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = L[n](subs(sol, aL), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = L[n](subs(sol, aL), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   DElist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f*x+g, x/f^2)));
      taux := factor(subs(sol, subs(x = f*x+g, (-x + aL + 1)/f)));
      lambdan := factor(subs(sol, subs(x = f*x+g, n)));
      DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
      DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
      DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
      density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x))); 

      
      sigmaz := factor(coeff(DE, term1)); 
      tauz := factor(coeff(DE, term2)); 
      lambdaz := factor(coeff(DE, term3));

      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;
      #intervallist := sort(intervallist, (a, b) -> evalb(a < b));

      DElist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = L[n](subs(sol, aL), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(DElist) > 1 then
   print("Warning, several solutions found");
   return(DElist);
end if;

end proc:




REtoHermite:= proc(RE, pn, x)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DE, DElist, density, parameters, f, g, i, j, interval:=[-infinity, infinity], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, N) > 2 or degree(Bdenom, N) > 2 or degree(Cnumer, N) > 4 or degree(Cdenom, N) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := 0;
Ctill := n/2;

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Hermite or a linear transformation";
end if;

parameters := remove(x -> member(x, {f, g}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x+g, 1/f^2)));
   taux := factor(subs(sol, subs(x = f*x+g, (-2*x)/f)));
   lambdan := factor(subs(sol, subs(x = f*x+g, 2*n)));
   DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
   DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
   DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
   density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x)));

   
   sigmaz := factor(coeff(DE, term1)); 
   tauz := factor(coeff(DE, term2)); 
   lambdaz := factor(coeff(DE, term3));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;
   #interval := sort(interval, (a, b) -> evalb(a < b));

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = H[n](subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = H[n](subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   DElist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f*x+g, 1/f^2)));
      taux := factor(subs(sol, subs(x = f*x+g, (-2*x)/f)));
      lambdan := factor(subs(sol, subs(x = f*x+g, 2*n)));
      DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
      DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
      DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
      density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x))); 

      
      sigmaz := factor(coeff(DE, term1)); 
      tauz := factor(coeff(DE, term2)); 
      lambdaz := factor(coeff(DE, term3));

      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;
      #intervallist := sort(intervallist, (a, b) -> evalb(a < b));

      DElist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = H[n](subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(DElist) > 1 then
   print("Warning, several solutions found");
   return(DElist);
end if;

end proc:




REtoBessel:= proc(RE, pn, x)
local p, n, re, ord, pnplus1, tn, An, Bn, Cn, A, aB, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DE, DElist, density, parameters, f, g, i, j, interval:=[0, infinity], intervallist;

p := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re,p(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
pnplus1 := expand((-coeff(re, p(n))*p(n)-coeff(re, p(n-1))*p(n-1))/coeff(re, p(n+1)));
if degree(pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(pnplus1, p(n)), x); 
Cn := -collect(coeff(pnplus1, p(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, N) > 2 or degree(Bdenom, N) > 2 or degree(Cnumer, N) > 4 or degree(Cdenom, N) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := 2*aB/((2*n+aB)*(2*n+aB+2));
Ctill := -4*n*(n+aB)/((2*n+aB-1)*(2*n+aB)^2*(2*n+aB+1));

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aB, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Bessel or a linear transformation";
end if;

parameters := remove(x -> member(x, {aB, f, g}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x+g, x^2/f^2)));
   taux := factor(subs(sol, subs(x = f*x+g, ((aB + 2)*x + 2)/f)));
   lambdan := factor(subs(sol, subs(x = f*x+g, -n*(n+aB+1))));
   DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
   DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
   DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
   density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x)));

   
   sigmaz := factor(coeff(DE, term1)); 
   tauz := factor(coeff(DE, term2)); 
   lambdaz := factor(coeff(DE, term3));

   for i to nops(interval) do 
     if interval[i] = infinity or interval[i] = -infinity then 
        interval[i] := interval[i];
     else 
        interval[i] := subs(sol, simplify((interval[i] - g)/f)); 
     end if;
   end do;
   #interval := sort(interval, (a, b) -> evalb(a < b));

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   DElist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 
      intervallist := [];

      sigmax := factor(subs(sol, subs(x = f*x+g, x^2/f^2)));
      taux := factor(subs(sol, subs(x = f*x+g, ((aB + 2)*x + 2)/f)));
      lambdan := factor(subs(sol, subs(x = f*x+g, -n*(n+aB+1))));
      DE := sigmax*diff(p(n, x), x$2) + taux*diff(p(n, x), x) + lambdan*p(n, x);
      DE := subs(diff(p(n, x), x$2) = term1, diff(p(n, x), x) = term2, p(n, x) = term3, DE);
      DE := collect(expand(numer(simplify(DE))), [term1, term2, term3]);
      density := simplify(1 / coeff(DE, term1) * exp(int(coeff(DE, term2) / coeff(DE, term1), x))); 

      
      sigmaz := factor(coeff(DE, term1)); 
      tauz := factor(coeff(DE, term2)); 
      lambdaz := factor(coeff(DE, term3));

      for j to nops(interval) do 
        if interval[j] = infinity or interval[j] = -infinity
          then intervallist := [op(intervallist), interval[j]];
        else 
          intervallist := [op(intervallist), subs(sol, simplify((interval[j]-g)/f))];
        end if;
      end do;
      #intervallist := sort(intervallist, (a, b) -> evalb(a < b));

      DElist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[n] = lambdaz,
      p(n, x) = y[n](subs(sol, aB), subs(sol, subs(x = f*x + g, x))), w(x) = density,
      k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(DElist) > 1 then
   print("Warning, several solutions found");
   return(DElist);
end if;

end proc:




REtoDE := proc(RE, pn, x)
    local results, result, sub_funcs, f, func_name, func_proc, i;
    results := [];

    sub_funcs := [
        ["Has a solution as Jacobi", REtoJacobi],
        ["Has a solution as Laguerre", REtoLaguerre],
        ["Has a solution as Hermite", REtoHermite],
        ["Has a solution as Bessel", REtoBessel]
    ];

    
    for i from 1 to nops(sub_funcs) do
        func_name := sub_funcs[i][1];
        func_proc := sub_funcs[i][2];
        try
            result := func_proc(RE, pn, x);
            results := [op(results), [func_name, result]];
        catch:
            # skip on error
        end try;
    end do;

    if nops(results) > 0 then
        return results;
    else
        error "No solution found";
    end if;
end proc:



###############################################################################



REtoMeixner:= proc(RE, pn, x)
local P, n, re, ord, Pnplus1, tn, An, Bn, Cn, A, bM, cM, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

P := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, P(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
Pnplus1 := expand((-coeff(re, P(n))*P(n)-coeff(re, P(n-1))*P(n-1))/coeff(re, P(n+1)));
if degree(Pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(Pnplus1, P(n)), x); 
Cn := -collect(coeff(Pnplus1, P(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, M) > 2 or degree(Bdenom, M) > 2 or degree(Cnumer, M) > 6 or degree(Cdenom, M) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (cM*bM+(cM+1)*n)/(cM-1);
Ctill := (bM*cM*n+cM*n^2-cM*n)/(cM^2-2*cM+1);

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {bM, cM, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Meixner or a linear transformation";
end if;

parameters := remove(x -> member(x, {bM, cM, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x + g, x)));
   taux := factor(subs(sol, subs(x = f*x + g, cM*bM+(cM-1)*x)));
   lambdan := factor(subs(sol, subs(x = f*x + g, -(cM-1)*n)));
   DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
   DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
   density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));
 
   sigmaz := factor(coeff(DI, term1)); 
   tauz := factor(coeff(DI, term2)); 
   lambdaz := factor(coeff(DI, term3)); 
    
   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bM), subs(sol, cM), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bM), subs(sol, cM), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 

      sigmax := factor(subs(sol, subs(x = f*x + g, x)));
      taux := factor(subs(sol, subs(x = f*x + g, cM*bM+(cM-1)*x)));
      lambdan := factor(subs(sol, subs(x = f*x + g, -(cM-1)*n)));
      DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
      DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
      density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));

      sigmaz := factor(coeff(DI, term1)); 
      tauz := factor(coeff(DI, term2)); 
      lambdaz := factor(coeff(DI, term3)); 

      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = M[n](subs(sol, bM), subs(sol, cM), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:




REtoCharlier:= proc(RE, pn, x)
local P, n, re, ord, Pnplus1, tn, An, Bn, Cn, A, aC, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

P := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, P(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
Pnplus1 := expand((-coeff(re, P(n))*P(n)-coeff(re, P(n-1))*P(n-1))/coeff(re, P(n+1)));
if degree(Pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(Pnplus1, P(n)), x); 
Cn := -collect(coeff(Pnplus1, P(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, M) > 2 or degree(Bdenom, M) > 2 or degree(Cnumer, M) > 6 or degree(Cdenom, M) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -n-aC;
Ctill := aC*n;

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aC, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Charlier or a linear transformation";
end if;

parameters := remove(x -> member(x, {aC, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x + g, x)));
   taux := factor(subs(sol, subs(x = f*x + g, aC-x)));
   lambdan := factor(subs(sol, subs(x = f*x + g, n)));
   DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
   DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
   density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));
 
   sigmaz := factor(coeff(DI, term1)); 
   tauz := factor(coeff(DI, term2)); 
   lambdaz := factor(coeff(DI, term3)); 
    
   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
   elif is(subs(sol, f) < 0) then 
      interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = C[n](subs(sol, aC), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = C[n](subs(sol, aC), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 

      sigmax := factor(subs(sol, subs(x = f*x + g, x)));
      taux := factor(subs(sol, subs(x = f*x + g, aC-x)));
      lambdan := factor(subs(sol, subs(x = f*x + g, n)));
      DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
      DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
      density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));

      sigmaz := factor(coeff(DI, term1)); 
      tauz := factor(coeff(DI, term2)); 
      lambdaz := factor(coeff(DI, term3)); 

      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", infinity];
      elif is(subs(sol, f) < 0) then 
         interval := [-infinity, "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = C[n](subs(sol, aC), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:





REtoKrawtchouk:= proc(RE, pn, x)
local P, n, re, ord, Pnplus1, tn, An, Bn, Cn, A, pK, NK, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

P := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, P(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
Pnplus1 := expand((-coeff(re, P(n))*P(n)-coeff(re, P(n-1))*P(n-1))/coeff(re, P(n+1)));
if degree(Pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(Pnplus1, P(n)), x); 
Cn := -collect(coeff(Pnplus1, P(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, M) > 2 or degree(Bdenom, M) > 2 or degree(Cnumer, M) > 6 or degree(Cdenom, M) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := (2*n-NK)*pK-n;
Ctill := (n^2+(-NK-1)*n)*pK^2+((NK+1)*n-n^2)*pK;

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {pK, NK, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Krawtchouk or a linear transformation";
end if;

parameters := remove(x -> member(x, {pK, NK, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x + g, x)));
   taux := factor(subs(sol, subs(x = f*x + g, pK*NK/(-pK+1)-x*(1+pK/(-pK+1)))));
   lambdan := factor(subs(sol, subs(x = f*x + g, n/(1-pK))));
   DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
   DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
   density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));
 
   sigmaz := factor(coeff(DI, term1)); 
   tauz := factor(coeff(DI, term2)); 
   lambdaz := factor(coeff(DI, term3)); 
    
   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NK)/f)]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NK)/f)];
   elif is(subs(sol, f) < 0) then 
      interval := [subs(sol, (-g+NK)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pK), subs(sol, NK), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pK), subs(sol, NK), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 

      sigmax := factor(subs(sol, subs(x = f*x + g, x)));
      taux := factor(subs(sol, subs(x = f*x + g, pK*NK/(-pK+1)-x*(1+pK/(-pK+1)))));
      lambdan := factor(subs(sol, subs(x = f*x + g, n/(1-pK))));
      DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
      DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
      density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));

      sigmaz := factor(coeff(DI, term1)); 
      tauz := factor(coeff(DI, term2)); 
      lambdaz := factor(coeff(DI, term3)); 

      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NK)/f)]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NK)/f)];
      elif is(subs(sol, f) < 0) then 
         interval := [subs(sol, (-g+NK)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = K[n](subs(sol, pK), subs(sol, NK), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:





REtoHahn:= proc(RE, pn, x)
local P, n, re, ord, Pnplus1, tn, An, Bn, Cn, A, aH, bH, NH, tillB, tillC, Bnumer, Bdenom, Cnumer, Cdenom, Btill, Ctill, Btillnumer, Btilldenom, Ctillnumer, Ctilldenom, eqB, eqC, Bvars, Cvars,
Sol, varz, solutions, sol, sigmax, taux, lambdan, sigmaz, tauz, lambdaz, DI, Dllist, density, parameters, f, g, i, interval;

P := op(0,pn);
n := op(1,pn);

if type(RE, `=`) then re := lhs(RE)-rhs(RE) else re := RE end if;

re := numer(normal(re));

ord := `recursion/order`(re, P(n)); 
if not(ord = 2) then 
   error "Not a three term recurrence equation";
end if;

re := subs(n = n - 1, re);
Pnplus1 := expand((-coeff(re, P(n))*P(n)-coeff(re, P(n-1))*P(n-1))/coeff(re, P(n+1)));
if degree(Pnplus1, x) <= 0 then
    error "Wrong type of three term recurrence equation";
end if;

tn := collect(coeff(Pnplus1, P(n)), x); 
Cn := -collect(coeff(Pnplus1, P(n-1)), x);

if degree(tn, x) <> 1 or degree(Cn, x) <> 0 then
    error "No classical orthogonal polynomial exists";
end if;

tn := collect(expand(subs(x = (x - g)/f, tn)), x);
An := coeff(tn, x, 1);
Bn := coeff(tn, x, 0);

A := normal(An);

if An = 0 then 
    error "No classical orthogonal polynomial exists";
end if;

tillB := factor(normal(Bn/An));
tillC := factor(normal(Cn/(An*subs(n = n - 1, An))));

Bnumer := collect(expand(numer(tillB)), n);
Bdenom := collect(expand(denom(tillB)), n);
Cnumer := collect(expand(numer(tillC)), n);
Cdenom := collect(expand(denom(tillC)), n);

if degree(Bnumer, M) > 2 or degree(Bdenom, M) > 2 or degree(Cnumer, M) > 6 or degree(Cdenom, M) > 4 then 
    error "No classical orthogonal polynomial exists";
end if;

Btill := -(NH*aH^2+NH*aH*bH+2*NH*aH*n+2*NH*bH*n+2*NH*n^2-aH^2*n-aH*n^2+bH^2*n+bH*n^2+NH*aH+NH*bH+2*NH*n-aH*n+bH*n)/((2*n+bH+aH)*(2*n+bH+aH+2));
Ctill := -n*(n-NH-1)*(n+aH)*(n+bH)*(n+bH+aH)*(n+bH+aH+NH+1)/((2*n+bH+aH-1)*(2*n+bH+aH)^2*(2*n+bH+aH+1));

Btillnumer := collect(expand(numer(Btill)), n);
Btilldenom := collect(expand(denom(Btill)), n);
Ctillnumer := collect(expand(numer(Ctill)), n);
Ctilldenom := collect(expand(denom(Ctill)), n);

eqB := collect(expand(-Bdenom*Btillnumer + Bnumer*Btilldenom), n);
eqC := collect(expand(-Cdenom*Ctillnumer + Cnumer*Ctilldenom), n);

Sol := {coeffs(eqB, n)}; 
Sol := {coeffs(eqC, n), op(Sol)};
varz := indets(Sol);

solutions := {solve(Sol, {aH, bH, NH, f, g}, explicit)};

if solutions = {} then 
   solutions := solve(Sol, varz);
end if;

solutions := select(x -> not member(f = 0, x), solutions);

if solutions = {} then 
   error "This recurrence equation has no classical orthogonal polynomial solution as Hahn or a linear transformation";
end if;

parameters := remove(x -> member(x, {aH, bH, NH, f, g, q}), indets(solutions));

if nops(solutions) = 1 then
   sol := op(solutions);

   sigmax := factor(subs(sol, subs(x = f*x + g, x*(bH+NH+1-x))));
   taux := factor(subs(sol, subs(x = f*x + g, NH*(aH+1)-x*(aH+bH+2))));
   lambdan := factor(subs(sol, subs(x = f*x + g, n*(n+bH+aH+1))));
   DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
   DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
   DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
   density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));
 
   sigmaz := factor(coeff(DI, term1)); 
   tauz := factor(coeff(DI, term2)); 
   lambdaz := factor(coeff(DI, term3)); 
    
   interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)]; 
   if is(subs(sol, f) > 0) then 
      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)];
   elif is(subs(sol, f) < 0) then 
      interval := [subs(sol, (-g+NH)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
   else 
      NULL; 
   end if;

   if parameters = {} then
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   else 
      print("Warning, parameters have the values", sol);
      return([sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval]);
   end if;
end if;

if nops(solutions) > 1 then 
   Dllist := convert(solutions, list); 

   if parameters <> {} then 
      print("Warning, parameters have the values", solutions);
   end if; 

   for i to nops(solutions) do 
      sol := op(i, solutions); 

      sigmax := factor(subs(sol, subs(x = f*x + g, x*(bH+NH+1-x))));
      taux := factor(subs(sol, subs(x = f*x + g, NH*(aH+1)-x*(aH+bH+2))));
      lambdan := factor(subs(sol, subs(x = f*x + g, n*(n+bH+aH+1))));
      DI := factor(sigmax * F(B(p(n, x)))) + factor(taux * F(p(n, x))) + factor(lambdan * p(n, x));
      DI := subs(F(B(p(n, x))) = term1, F(p(n, x)) = term2, p(n, x) = term3, DI);
      DI := collect(expand(numer(simplify(DI))), [term1, term2, term3]);
      density := factor((coeff(DI, term1) + coeff(DI, term2)) / subs(x = x + 1, coeff(DI, term1)));

      sigmaz := factor(coeff(DI, term1)); 
      tauz := factor(coeff(DI, term2)); 
      lambdaz := factor(coeff(DI, term3)); 

      interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)]; 
      if is(subs(sol, f) > 0) then 
         interval := [subs(sol, -g/f), subs(sol, (-g+1)/f), subs(sol, (-g+2)/f), "...", subs(sol, (-g+NH)/f)];
      elif is(subs(sol, f) < 0) then 
         interval := [subs(sol, (-g+NH)/f), "...", subs(sol, (-g+2)/f), subs(sol, (-g+1)/f), subs(sol, -g/f)];
      else 
         NULL;
      end if; 

      Dllist[i] := [sigma(x) = sigmaz, tau(x) = tauz, lambda[q, n] = lambdaz, 
      p(n, x) = Q[n](subs(sol, aH), subs(sol, bH), subs(sol, NH), subs(sol, subs(x = f*x+g, x))), 
      rho(q*x)/rho(x) = density, k[n+1]/k[n] = factor(subs(sol, A)), I = interval];
   end do;
end if;

if nops(Dllist) > 1 then
   print("Warning, several solutions found");
   return(Dllist);
end if;

end proc:






REtoDiscrete := proc(RE, pn, x)
    local results, result, sub_funcs, f, func_name, func_proc, i;
    results := [];

    sub_funcs := [
        ["Has a solution as Meixner", REtoMeixner],
        ["Has a solution as Charlier", REtoCharlier],
        ["Has a solution as Krawtchouk", REtoKrawtchouk],
        ["Has a solution as Hahn", REtoHahn]
    ];

    for i from 1 to nops(sub_funcs) do
        func_name := sub_funcs[i][1];
        func_proc := sub_funcs[i][2];
        try
            result := func_proc(RE, pn, x);
            results := [op(results), [func_name, result]];
        catch:
            # skip on error
        end try;
    end do;

    if nops(results) > 0 then
        return results;
    else
        error "No solution found";
    end if;
end proc:







































