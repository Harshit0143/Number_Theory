# Number Theory 

## Modular Inverse

* $Modular$ $Inverse$ of an integer $a$ with respect to a number $m$ is an integer $x$  such that:
$$a*x \equiv 1 \space (mod \space m) $$

* Baiscally:  
  - We have a number $m$ and numbers $a$ and $b$ s.t. $a \space mod \space b = 0$
  - We wish to find $(\frac{a}{b}\space mod \space m)̦$.
  - But we only have available $a \space mod \space  m$ and $b \space mod \space  m$
  - So we find the `modular inverse` of $b$ w.r.t. $m$ say $k$ then
  
  $$\frac{a}{b}\space mod \space m = (a*k)\space mod \space m = ( (a\space mod \space m)*k )\space mod \space m$$

## Getting the `modular inverse` 

1) Fermat’s Little Theorem 
2) Extended Euclidian Algorithm


### Fermat’s Little Theorem 
$$a^p \space mod \space  p = 1 $$
* For any `prime` $p$ and $gcd(a, p) = 1$

which can be used to derive:    
`Result`: modular inverse of $k$ $w.r.t.$  $p$ 		is $k^{p-2}$ 
* Conditions: 
1) $p$ is `prime` 
2) $k$ and $p$ are `coprime` 

#### Definiton 
$$(\frac{1}{k})^n \space mod \space p = (inv(k))^n \space mod \space p$$
* where $inv()$ represents the `modulo inverse` $w.r.t.$ $p$




 $$ \binom n r  \equiv (n! \space *\space  inv(r!)\space *\space inv(n-r)!)\space (mod \space  p)$$

### Properties : 
* For inverse $w.r.t$. any $m$
$$inv(x) = inv(x \space mod\space m)$$
* GiVEN $p$ is a `prime`:
$$a^b \equiv a^{b \space mod\space  (p-1)}\space  mod \space p$$


### Problem: [Prime Sum Game](https://atcoder.jp/contests/abc239/tasks/abc239_d)
* Under given constraints it can be solve using `Brute Force`.      
* Problem with constraints $1 \leq A, B, C, D \leq 10^9$
#### Algorithm:
  1) Build all `primes` in $[2,(B+D)]$
  2) `for` $i =  A, A+1 ….. B$<br>
	    $\space \space \space \space$ check if there is a prime in $[i+ C, i+ D]$ (binary search)<br>
		  $\space \space \space \space$ `if` there is no prime in $[i+ C, i+ D]$<br>
			 $\space \space \space \space$ $\space \space \space \space$    `Takahashi` chooses this number and wins<br>
    
  3) `Aoki` wins if there is no valid $i$<br>  






### General Idea:

* `Finding` something is same as checking if it’s `frequency == 0`. There is a `trade-off` between using a 
`map` and a `frequency array`.    
* A `frequency array` is a lot of time to `initiate` but later fast. `Map` is no time to initiate but `queries` take time.
#### [Common Divisor](https://usaco.guide/problems/cses-1081-common-divisors/solution)
The `frequency array` won in this problem 






### Definition 
$f()$ is a `Multiplicative function` $\iff$ $f(x*y) = f(x)f(y)$ whenever $gcd(x, y) = 1$


## # `Euler Totient function` 
* It is a multiplicative function 
 <p align="center">
 
 <img width="352" alt="Screenshot 2023-04-20 at 5 41 42 PM" src="https://user-images.githubusercontent.com/97736991/233362145-5d115e9a-2962-418a-8b5d-6bc3a72571f5.png">
 </p>
 
### # [Number of natural numbers](https://www.spoj.com/problems/ETF/#:~:text=ETF%20%2D%20Euler%20Totient%20Function&text=In%20number%20theory%2C%20the%20totient,%3C%3D%2010%5E6)  $\leq n$  `co-prime` with $n$
* This is the `Euler Totient` function 
* It can be evaluated in $O(\sqrt n)$ time without any `pre-computation` using the standard $O(\sqrt n$) time algorithm to calculate all prime factors
* If all `primes` are computed, it O(number of primes < n) where each `query` will be faster then previous method but still $O(\sqrt n)$ time (for large number of `queries`, though, it will be faster)


## Modular inverse for `non prime` case:
<p align="center">
<img width="239" alt="Screenshot 2023-04-20 at 5 40 00 PM" src="https://user-images.githubusercontent.com/97736991/233361779-1f2d01d8-ba9c-4f9d-83ad-c50fd44354e1.png"></p>

* Evaluating this however, takes $O(sqrt(a))$ time. we can get the `modulo inverse` in $O(log(a))$ time using the `Extended Euclid’s Algorithm`

<p align="center">
<img width="444" alt="Screenshot 2023-04-20 at 5 45 41 PM" src="https://user-images.githubusercontent.com/97736991/233362973-6041b21b-6680-49d7-85a6-97a29a09c35c.png"></p>



## Extended Euclid’s Algorithm: Solving [Linear Diophantine Equations](https://cp-algorithms.com/algebra/linear-diophantine-equation.html#algorithmic-solution)

`Note`: 
* The algorithm, by itself gives the value with minimum $|X|+ |Y|$ among all possible solutions. [See this](https://onlinejudge.org/index.php?option=com_onlinejudge&Itemid=8&page=show_problem&problem=1045).
* If there are multiple solutions, the one with $X <= Y$ is given.
Proof: I don’t know 
<p align="center">
<img width="601" alt="Screenshot 2023-04-20 at 5 46 23 PM" src="https://user-images.githubusercontent.com/97736991/233363172-c5c0da90-2555-471b-a220-440270434183.png"></p>



## [Number of Solutions](https://onlinejudge.org/index.php?option=com_onlinejudge&Itemid=8&page=show_problem&problem=4628)
For the equation : $$(ax + by = c)\space ; \space a , b , c >0$$
* You can find the number of positive solutions in $O(1)$ time  given that $a$ and  $b$ are `constant` and different `queries` on $c$ with some `pre computation`. 
### Algorithm: 
  1) Solve $(ax_0 + by_0 = g )$ ; $g = gcd(a, b)$
  2) For each query on $c$ :
    $x = \frac{x_0c}{g}, y = \frac{y_0c}{g}  ~~~~~~~~~~~if$ $c$ is divisible by $g$<br>
    no solution    $~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~$ $Otherwise$


### # [Counting Nuber of solutions](https://cp-algorithms.com/algebra/linear-diophantine-equation.html): 
* You can use basic math to get the expression for number of solutions. ̦
* [See solution](https://github.com/Harshit0143/Gift-Dilemma/tree/main)

<br><br>
# Problem Notes:
### # Composite Number 
Any `composite` number $n$ can be written as a product of $2$ numbers i.e. $n = x*y$ for integers $x$ and $y$

### # How to factories a number a given list of all primes?

1) Iterate over all $primes  \space \leq \space \sqrt a$ and keep dividng buy then `ENTIRELY`
2) The remaining $a$ is either $1$ or $prime$.  
```
  while prime[i]*prime[i] <= a_curr       ### NOTE  (a) is changing
    a_curr /= prime[i]
```
#### `VERY IMPORTANT`:
  * Emplhasize: in $(1)$ we check for `primes` $\leq \sqrt a$.
  * For $a \leq 10^9$ you need just $\approx \sqrt{10^9} = 31623$ numbers which have just $3401$ primes. 
  * You `DON'T` need to build all `primes` till $10^9$, build till $\sqrt{10^9}$
* YES `a_curr` works and it’s tighter
* Why `a_curr`, not just `a` works?
  * It’s like for the remaining $n$ we know that each `prime factor` ($\leq \sqrt {remaining \space a}$ ).   
  * But for the $remaining \space a$ note that we already know any of the smaller prime is not a divisor so we have `Jump Started`





###  # $n$ has $O(\sqrt n )$ divisors
  #### Proof <br>
The Algorithm of finding divisors of $n$<br>
     
     
### # Largest prime factor 
* `If` $n$ is prime `then` the largest prime factor of $n$ is $n$
* `Else` th largest prime factor of $n \leq \frac{n}{2}$
  #### Proof<br>
 * `If`: $n$ is prime then done
 * `Else`: there exists a `prime` $p$ such that 
 * $p*k = n$ for some $k \geq̦ 2$
    * Why $k \geq 2$?<br> 
    If $k=1$ then $n$ is `prime` which is not the case<br>
    $\implies p = \frac{n}{k} \implies p \leq \frac{n}{2}$<br>



### # $n$ has $O(log(n))$ prime factors
  #### Proof <br>

let $p_1....p_k$ be the prime factors of $n$<br>
$\implies p_1^{a_1}.....p_k^{a_k}  = n$ where $a_i \geq 1$ $for$ $i = 1....k$<br>
$\implies p_1*p_2……p_k \leq n$<br>
Note that $p_i \leq 2$ for every $i$<br>
$\implies 2^k \leq n\implies k \leq log(n)$<br>




### # [Soldiers and Number Game](https://codeforces.com/problemset/problem/546/D)
* This is amazing and now you can get all `prime factors` of a number $a$  in $O(log(a))$ time with $O(a*log(a))$ pre-processing 
* This obviosly is in line with the cast that any number $a$ as atmost $log(a)$ prime factors 





### # [1729](https://codeforces.com/gym/423169/problem/B)
* Notice how we have created all possible multiple of the `given primes` at the last.
* Using a `dp` like idea, adding each `prime` one by one
* Following is a `beautiful` code to produce all numbers $\leq$ `L` `producable` by `primes` 

```
  	vector<int> ans;
    ans.push_back(1);
    for (int p: primes)
    {
    
        for (int i = 0; i < ans.size(); i++)
            { 
	    	if (ans[i]*p <= L)
                	ans.push_back(ans[i] * p);
	    }
    }
```



### # Number as sum of `primes`
* Every `even` number $> 2$ can be written as a sum of $2$ primes.

* Any `non-prime` `odd` number can be written as a sum of $2$ primes $\iff$ `number` = `prime` + 2

* Every other `non-prime` `odd` number can be written as sum of $3$ primes<br>
 	 `2 + even  ==> 2 + p1 + p2` 




### [Sum of Divisors](https://cses.fi/problemset/task/1082)



* The [efficient](https://usaco.guide/problems/cses-1082-sum-of-divisors/solution) computation of: 
 <p align="center">
<img width="441" alt="Screenshot 2023-04-20 at 5 56 39 PM" src="https://user-images.githubusercontent.com/97736991/233365503-cce3cbb0-cd34-4e7f-8f1a-6470fb93eb7d.png"></p>


 
can be done in $O(\sqrt n)$ time.
* Infact sum over $k$ for [any](https://codeforces.com/problemset/problem/1561/D1) $f( \left\lfloor \frac{n}{k} \right\rfloor)$ 

### # $O(n\*2^n)$ fitting hints `Principal of Inclusion exclusion`



### # [GCD Counting](https://codeforces.com/problemset/problem/1101/D) 
It is an awesome problem requiring proofs used above and also some “Reverse Counting Principal”


Total DFS time: O(sum of number of vertices)
Sum = O(sum of number of divisors of each prime)
== O(number of prime factors of each number)
{Reverse counting. 









Proof
Make a bipartite graph G1 a —-> prime IFF (prime) divides (a). 
* Number of edges = Sum of number of prime divisors of each number ~ n*log(a) }
Now consider the graph G2  p —-> IFF prime divides (a)
You can show that an edge (a->p) is in G1 <==> (p—->a) is in G2
Number of edges in G2 = Required nodes to visit for BFS
Number of edges in G1 = n*log(a) 
So we need to do atmost n*log(a) need to work in all DFS if we do it wisely which is Awesome 

n*p was being done earlier where p == O(n^(2/3))
n*log(a) is the max word where log(q) == P(log(n)) Here

But we can’t do O(p*n) work obviously in choosing the allowed vertices in the graph
Sieve so that we hit only the valid points
p, 2*p, 3*p………… Somehow take these vertices only
But Again How
log(log(n)): Store in each node, the graph to belongs to
To make all graphs we can take O(log(n)*a) time 
Iterate over each edge. Push it into every graph bucket it belongs to. TRUST ME. Pushing only vertices into the bucket won’t work,
How to decide which bucket to put an edge in? 
Common divisor of both ends of the edge. Takes O(sqrt(a)*E) time ~ O(2e5 *1.5e(2.5)) ~O(3e(7.5))
Now for each graph, we have the edges in it. Notice that the sum of edges in all graphs <= O(n*log(a))
Following is the part where I was blocked. But i realised using map<,> won’t take a lot of time but to the upper limit on sum of number of vertices in each graph
Use an STL map to construct an adjacency list of. The access time is each time log(n) but the number of vertices is not very large so total sum of times for all DFS’s is O(n*log(a)*log(n))  Which should work






