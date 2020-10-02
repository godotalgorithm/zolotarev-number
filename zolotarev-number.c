/* Zolotarev number evaluation for finite unions of closed intervals */

/* compile into an executable as-is to use the command-line interface
   OR
   remove the main & compile into a library to use the function interface */

/* command-line interface for calculating Zolotarev numbers:
   USAGE: <executable> <order of the Zolotarev number> <input file for 1st set> <input file for 2nd set>

   input file format for sets:
   <number of closed intervals>
   <left endpoint of 1st interval> <right endpoint of 1st interval>
   <left endpoint of 2nd interval> <right endpoint of 2nd interval>
   ...
   <left endpoint of last interval> <right endpoint of last interval>

   NOTE: all endpoints should be in increasing ordered */

/* prototype of function interface for calculating Zolotarev numbers */
double zolotarev_number(int n, /* order of the Zolotarev number */
                        int num1, /* number of intervals in the 1st set */
                        int num2, /* number of intervals in the 2nd set */
                        double *left1, /* left endpoints of the 1st set in increasing order [num1] */
                        double *left2, /* left endpoints of the 2nd set in increasing order [num2] */
                        double *right1, /* right endpoints of the 1st set in increasing order [num1] */
                        double *right2, /* right endpoints of the 2nd set in increasing order [num2] */
                        double *root, /* on output, roots of the optimal rational function [n] */
                        double *pole, /* on output, poles of the optimal rational function [n] */
                        double *scale, /* on output, prefactor of the optimal rational function [1] */
                        double *conum1, /* on output, condition number on the 1st set [1] */
                        double *conum2, /* on output, condition number on the 2nd set [1] */
                        int *info); /* on output, status of the calculation [1] */
/* RETURN: value of the Zolotarev number */

/*  possible status values:
        info == -N: trivial Zolotarev solution with order reduced by N
        info == 0: successful calculation of Zolotarev number with full order
        info == 1: misordering detected in 1st set
        info == 2: misordering detected in 2nd set
        info == 3: misordering detected between sets
        info == 4: numerical pinning of a root or pole has prevented convergence
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

/* common but nonstandard POSIX definition of pi */
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

/* maximum number of iterations of the ascending Landen transformation needed at double precision */
#define MAX_ITER_DN 15

/* maximum number of iterations for root finding */
#define MAX_ITER_ROOT 50

/* tolerance for secant method to identify the step before expected convergence */
#define SECANT_TOL 1e-11

/* tolerance for Newton's method to identify the step before expected convergence */
#define NEWTON_TOL 1e-9

/* tolerance for the golden section search */
#define GOLDEN_TOL 1e-7

/* log-tolerance for linear search step underflow */
#define STEP_TOL 34.0

/* maximum number of iterations in the numerical solver */
#define MAX_ITER 1000

/* locate a point in a finite union of closed intervals using a binary search */
int locate(double x, /* point to locate */
           int num, /* number of intervals in the set */
           double *left, /* left endpoints of the set in increasing order [num] */
           double *right) /* left endpoints of the set in increasing order [num] */
/* RETURN: +i if x is in the interval [left[i], right[i]],
           -i if x is in the gap between right[i-1] & left[i] */
{
    int lower = 0, upper = num-1;
    if(x <= right[0]) { return 0; }
    if(x >= left[num-1]) { return num-1; }
    while (lower+1 != upper)
    {
        int mid = (lower+upper)/2;
        if(x < left[mid]) { upper = mid; }
        else { lower = mid; }
    }

    if(x <= right[lower]) { return lower; }
    return -upper;
}

/* construct a Mobius transformation, z |-> (map[0]*z + map[1])/(map[2]*z + map[3]),
   to the standard domain of [lambda, 1] for the 1st set & [-1, -lambda] for the 2nd set */
double mobius_setup(int num1, /* number of intervals in the 1st set */
                    int num2, /* number of intervals in the 2nd set */
                    double *map, /* coefficients of the Mobius transformation [4] */
                    double *left1, /* left endpoints of the 1st set in increasing order [num1] */
                    double *left2, /* left endpoints of the 2nd set in increasing order [num2] */
                    double *right1, /* right endpoints of the 1st set in increasing order [num1] */
                    double *right2, /* right endpoints of the 2nd set in increasing order [num2] */
                    int *info) /* on output, status of the calculation [1] */
/* RETURN: lambda value for the mapped domain */
{
    int i;
    double lambda, xmin, xmax, ymin, ymax;

    /* check ordering of sets */
    for(i=0 ; i<num1 ; i++)
    { if(left1[i] > right1[i]) { *info = 1; return 0.0; } }
    for(i=1 ; i<num1 ; i++)
    { if(right1[i-1] > left1[i] || left1[i-1] == left1[i] || right1[i-1] == right1[i]) { *info = 1; return 0.0; } }
    for(i=0 ; i<num2 ; i++)
    { if(left2[i] > right2[i]) { *info = 2; return 0.0; } }
    for(i=1 ; i<num2 ; i++)
    { if(right2[i-1] > left2[i] || left2[i-1] == left2[i] || right2[i-1] == right2[i]) { *info = 2; return 0.0; } }

    /* find mapped endpoints of the sets */
    xmin = left1[0];
    xmax = right1[num1-1];
    ymin = left2[0];
    ymax = right2[num2-1];

    if(xmin < ymin && xmax > ymax) /* 1st set encompasses the 2nd set */
    {
        i = locate(ymin, num1, left1, right1);
        if(i >= 0) { *info = 3; return 0.0; }
        xmin = left1[-i];
        xmax = right1[-i-1]; 
    }
    else if(xmin > ymin && xmax < ymax) /* 2nd set encompasses the 1st set */
    {
        i = locate(xmin, num2, left2, right2);
        if(i >= 0) { *info = 3; return 0.0; }
        ymin = left2[-i];
        ymax = right2[-i-1];
    }
    else if( (xmin < ymin && xmax > ymin) || (xmin < ymax && xmax > ymax) ) /* input sets cannot be mapped to ordered sets */
    { *info = 3; return 0.0; }

    /* calculate lambda & the transformation coefficients */
    lambda = sqrt(fabs((xmax-xmin)*(ymax-ymin))) - sqrt(fabs((xmax-ymax)*(xmin-ymin)));
    lambda = lambda*lambda/fabs((xmin-ymax)*(xmax-ymin));
    map[0] = -(1.0-lambda)*xmin*xmax + (1.0+lambda)*ymax*xmax - 2.0*lambda*ymax*xmin;
    map[1] = -(1.0-lambda)*lambda*xmin*xmax - (1.0+lambda)*lambda*ymax*xmax + 2.0*lambda*ymax*xmin;
    map[2] = (1.0-lambda)*ymax - (1.0+lambda)*xmin + 2.0*lambda*xmax;
    map[3] = (1.0-lambda)*lambda*ymax + (1.0+lambda)*lambda*xmin - 2.0*lambda*xmax;

    *info = 0;
    return lambda;
}

/* apply a Mobius transformation or its inverse */
double mobius(double z, /* point that is being transformed */
              double *map) /* 4 points defining the transformation [4] */
/* RETURN: value of transformed point */
{ return (map[0]*z + map[1])/(map[2]*z + map[3]); }
double mobius_inv(double z, /* point that is being transformed */
                  double *map) /* 4 points defining the transformation [4] */
/* RETURN: value of transformed point */
{
    if(fabs(z) == INFINITY)
    { return -map[3]/map[2]; }
    return (map[3]*z - map[1])/(-map[2]*z + map[0]);
}

/* elliptic integral of the 1st kind via the Arithmetic Geometric Mean (AGM) algorithm */
double elliptic_K(double k_prime) /* convenient transformation of the function argument, k_prime = sqrt(1 - k^2) */
/* RETURN: value of K(k') = K'(k), where k' = sqrt(1 - k^2) */
{
  double a = 1.0, b = k_prime, c = 1.0;

  if(k_prime < 0.0 || k_prime > 1.0)
  { printf("ERROR: argument of K must be in [0,1]\n"); exit(1); }
  while( a != a-c ) /* stagnation termination */
  {
    c = 0.5*(a-b);
    b = sqrt(a*b);
    a -= c;
  }
  return 0.5*M_PI/a;
}

/* delta amplitude, one of the Jacobi elliptic functions, via ascending Landen transformations
   NOTE: the descending Landen transformation can be faster for k_prime ~= 1, but it is numerically unstable in its native form
   NOTE: this is most accurate for small u; large u values can be mapped to small u values based on the period of dn, 4*K(k) */
double elliptic_dn(double u, /* 1st argument of dn(u,k) */
                   double k_prime) /* convenient transformation of 2nd argument of dn(u,k), k_prime = sqrt(1 - k^2) */
/* RETURN: value of dn(u,k) */
{
    int i = 0, j;
    double dn, k_map[MAX_ITER_DN];

    if(k_prime < 0.0 || k_prime > 1.0)
    { printf("ERROR: 2nd argument of dn must be in [0,1]\n"); exit(1); }
    if(k_prime == 1.0)
    { return 1.0; }
    
    k_map[0] = k_prime;
    while(k_map[i] != 0.0)
    {
        double k_pow2 = k_map[i]*k_map[i];

        if(i == MAX_ITER_DN-1)
        { printf("ERROR: maximum iteration exceeded in elliptic_dn\n"); exit(1); }

        k_map[++i] = k_pow2/(2.0 - k_pow2 + 2.0*sqrt(1.0 - k_pow2));
        u /= 1.0 + k_map[i];
    }
    dn = 1.0/cosh(u);
    for(j=i-1 ; j>0 ; j--)
    { dn = (dn+k_map[j]/dn)/(1.0+k_map[j]); }
    return dn;
}

/* check for trivial & analytical solutions */
double zolotarev_check(int n, /* order of the Zolotarev number */
                       int num1, /* number of intervals in the 1st set */
                       int num2, /* number of intervals in the 2nd set */
                       double lambda, /* lambda value of the Mobius transformation */
                       double *map, /* mapping coefficients of the Mobius transformation [4] */
                       double *left1, /* left endpoints of the 1st set in increasing order [num1] */
                       double *left2, /* left endpoints of the 2nd set in increasing order [num2] */
                       double *right1, /* right endpoints of the 1st set in increasing order [num1] */
                       double *right2, /* right endpoints of the 2nd set in increasing order [num2] */
                       double *root, /* on output, roots of the optimal rational function [n] */
                       double *pole, /* on output, poles of the optimal rational function [n] */
                       double *scale, /* on output, prefactor of the optimal rational function [1] */
                       int *info) /* on output, status of the calculation [1] */
/* RETURN: Zolotarev number of a valid solution, otherwise -1.0 */
{
    int i, left_degen = 0, right_degen = 0, analytical = 1;
    double max_error, Kp = elliptic_K(lambda);
    *info = 0;
    *scale = 1.0; /* value for analytical solutions, irrelevant to trivial solutions */

    /* check for trivial solutions */
    if(num1 <= n)
    {
        left_degen = 1;
        for(i=0 ; i<num1 ; i++)
        { if(left1[i] != right1[i]) { left_degen = 0; } }
    }
    if(num2 <= n)
    {
        right_degen = 1;
        for(i=0 ; i<num2 ; i++)
        { if(left2[i] != right2[i]) { right_degen = 0; } }
    }
    if(left_degen == 1 || right_degen == 1)
    { max_error = 0.0; }
    if(left_degen == 1 && right_degen == 1 && num1 == num2)
    {
        *info = num1 - n;
        for(i=0 ; i<num1 ; i++)
        {
            root[i] = mobius_inv(left1[i],map);
            pole[i] = mobius_inv(left2[i],map);
        }
    }
    else if(left_degen == 1 && (right_degen == 0 || num1 < num2))
    {
        *info = num1 - n;
        for(i=0 ; i<num1 ; i++)
        {
            root[i] = mobius_inv(left1[i],map);
            pole[i] = -elliptic_dn(Kp*(1.0 - ((double)i+0.5)/(double)num1),lambda);
        }
    }
    else if(right_degen == 1 && (left_degen == 0 || num2 < num1))
    {
        *info = num2 - n;
        for(i=0 ; i<num2 ; i++)
        {
            root[i] = elliptic_dn(Kp*(1.0 - ((double)i+0.5)/(double)num2),lambda);
            pole[i] = mobius_inv(left2[i],map);
        }
    }

    /* check for analytical solutions */
    if(left_degen == 0 && right_degen == 0)
    {
        for(i=1 ; i<n ; i++)
        {
            double ext = elliptic_dn(Kp*(1.0 - (double)i/(double)n),lambda);
            if(locate(mobius( ext,map), num1, left1, right1) < 0 ||
               locate(mobius(-ext,map), num2, left2, right2) < 0)
            { analytical = 0; }
        }

        if(analytical)
        {
            max_error = 1.0;
            for(i=0 ; i<n ; i++)
            {
                root[i] = elliptic_dn(Kp*(1.0 - ((double)i+0.5)/(double)n),lambda);
                pole[i] = -root[i];
                max_error *= ((1.0 - root[i])*(1.0 - root[i]))/((1.0 + root[i])*(1.0 + root[i]));
            }
        }
    }

    /* output when trivial & analytical solutions aren't valid */
    if(left_degen == 0 && right_degen == 0 && analytical == 0)
    { max_error = -1.0; }

    return max_error;
}

/* invert the Zolotarev mapping function dn(Kp*(1.0 - x), lambda) using the secant method */
double dn_inv(double val, /* value of the map */
              double Kp, /* scale factor for 1st argument of dn */
              double lambda) /* 2nd argument of dn */
/* RETURN: x term in 1st argument of the mapping function that produces val */
{
    int iter = 0, not_converged = 1, almost_converged = 0;
    double arg1, val1, arg2, val2;

    /* snap back out of bounds solutions */
    if(val <= lambda) { return 0.0; }
    if(val >= 1.0) { return 1.0; }

    /* initial guess for the inverse (small lambda limit) */
    arg1 = 1.0 - log(val)/log(lambda);
    val1 = elliptic_dn(Kp*(1.0 - arg1), lambda);
    if(arg1 < 0.5) { arg2 = arg1 + 1e-7; }
    else { arg2 = arg1 - 1e-7; }
    val2 = elliptic_dn(Kp*(1.0 - arg2), lambda);

    while(not_converged)
    {
        double arg3 = (arg2*(val - val1) + arg1*(val2 - val))/(val2 - val1);
        double val3 = elliptic_dn(Kp*(1.0 - arg3), lambda);
        val1 = val2;
        arg1 = arg2;
        val2 = val3;
        arg2 = arg3;
        if(val2 == val)
        { return arg2; }
        if(almost_converged)
        { not_converged = 0; }
        if(fabs(val2-val) < SECANT_TOL*fabs(val))
        { almost_converged = 1; }
        if(++iter == MAX_ITER_ROOT)
        { printf("ERROR: maximum iteration exceeded in dn_inv\n"); exit(1); }      
    }
    return arg2;
}

/* inital guess for a Zolotarev number minimizer */
void zolotarev_guess(int n, /* order of the Zolotarev number */
                     int num, /* number of intervals in the set */
                     double lambda, /* lambda value of the Mobius transformation, negative sign denotes [-lambda,-1] domain */
                     double *map, /* mapping coefficients of the Mobius transformation [4] */
                     double *left, /* left endpoints of the set in increasing order [num] */
                     double *right, /* right endpoints of the set in increasing order [num] */
                     double *root) /* on output, trial roots of the rational function [n] */
{
    int i, unconverged = 1, lambda_flip = 0;
    double Kp = elliptic_K(fabs(lambda)), *ext = (double*)malloc(sizeof(double)*(n+1));

    /* temporarily flip Mobius transformation for [-lambda,-1] domain */
    if(lambda < 0.0)
    { lambda = -lambda; map[0] = -map[0]; map[2] = -map[2]; lambda_flip = 1; }

    /* assign valid initial values to ext by sequential insertion to most distant point */
    ext[0] = 0.0;
    ext[1] = 1.0;
    for(i=1 ; i<n ; i++)
    {
        /* find most distant point */
        int j, max_index = 0;
        double max_ext = 0.0, max_dist = 0.0;
        for(j=0 ; j<i ; j++)
        {
            /* find most distant point between ext[j] & ext[j+1] */
            double new_ext = 0.5*(ext[j+1]+ext[j]), new_dist = 0.5*(ext[j+1]-ext[j]);
            int loc = locate(mobius(elliptic_dn(Kp*(1.0-new_ext),lambda),map), num, left, right);
            if(loc < 0)
            {
                double new_ext1 = dn_inv(mobius_inv(right[-loc-1],map), Kp, lambda);
                double new_ext2 = dn_inv(mobius_inv(left[-loc],map), Kp, lambda);
                double new_dist1 = ext[j+1]-new_ext1, new_dist2 = ext[j+1]-new_ext2;
                if(new_ext1-ext[j] < new_dist1) { new_dist1 = new_ext1-ext[j]; }
                if(new_ext2-ext[j] < new_dist2) { new_dist2 = new_ext2-ext[j]; }
                if(new_dist1 > new_dist2)
                { new_dist = new_dist1; new_ext = new_ext1; }
                else
                { new_dist = new_dist2; new_ext = new_ext2; }
            }

            if(new_dist > max_dist)
            {
                max_index = j+1;
                max_ext = new_ext;
                max_dist = new_dist;
            }
        }

        /* insert most distant point */
        for(j=i+1 ; j>max_index ; j--)
        { ext[j] = ext[j-1]; }
        ext[max_index] = max_ext;
    }

    /* assign equidistant values to roots */
    for(i=0 ; i<n ; i++)
    { root[i] = elliptic_dn(Kp*(1.0 - 0.5*(ext[i]+ext[i+1])), lambda); }

    /* reverse Mobius transformation & trial roots for [-lambda,-1] domain */
    if(lambda_flip)
    {
        map[0] = -map[0]; map[2] = -map[2];
        for(i=0 ; i<n ; i++) { root[i] = -root[i]; }
    }

    free(ext);
}

/* rational function in the objective function */
double rational(int n, /* number of roots/poles of the rational function */
                double z, /* point at which the rational function is evaluated */
                double *root, /* roots of the rational function [n] */
                double *pole) /* poles of the rational function [n] */
/* RETURN: prod_i (z - root[i])/(z - pole[i]) */
{
    int i;
    double ans = 1.0;

    for(i=0 ; i<n ; i++)
    { ans *= (z-root[i])/(z-pole[i]); }
    return ans;
}

/* 1st & 2nd logarithmic derivatives of the rational function in the objective function */
void dlog_rational(int n, /* number of roots/poles of the rational function */
                   double z, /* point at which the rational function is evaluated */
                   double *root, /* roots of the rational function [n] */
                   double *pole, /* poles of the rational function [n] */
                   double *deriv) /* 1st & 2nd logarithmic derivatives on output [2] */
{
    int i;

    deriv[0] = deriv[1] = 0.0;
    for(i=0 ; i<n ; i++)
    {
        double inv_root = 1.0/(z - root[i]), inv_pole = 1.0/(z - pole[i]);
        deriv[0] += inv_root - inv_pole;
        deriv[1] -= inv_root*inv_root - inv_pole*inv_pole;
    }
}

/* find a local extremum using bisection & Newton's method on a mapped domain */
double local_extremum(int n, /* number of roots/poles of the rational function */
                      double left, /* lower bound on the search interval */
                      double right, /* upper bound on the search interval */
                      double *root, /* roots of the rational function [n] */
                      double *pole) /* poles of the rational function [n] */
/* RETURN: location of the local extremum */
{
    int iter = 0, not_converged = 1, almost_converged = 0;
    double deriv[2], guess = 0.5*(left+right), dguess = left-right;

    while(not_converged)
    {
        /* Newton update w/ bisection failsafe */
        if(guess + dguess <= left || guess + dguess >= right)
        { guess = 0.5*(left + right); }
        else
        { guess += dguess; }

        /* update function value */
        dlog_rational(n, guess, root, pole, deriv);
        dguess = deriv[0]/fabs(deriv[1]);
        if(dguess > 0.0) { left = guess; }
        else { right = guess; }

        /* convergence criteria */
        if(almost_converged)
        { not_converged = 0; }
        if(fabs(dguess) < NEWTON_TOL*fabs(guess))
        { almost_converged = 1; }
        if(++iter == MAX_ITER_ROOT)
        { printf("ERROR: maximum iteration exceeded in local_extrema\n"); exit(1); }
    }
    return guess;
}

/* find all extrema of a rational function between its roots & in the approximation domain */
void all_extrema(int n, /* order of the Zolotarev number */
                 int num, /* number of intervals in the set */
                 double lambda, /* lambda value of the Mobius transformation, negative sign denotes [-lambda,-1] domain */
                 double *map, /* mapping coefficients of the Mobius transformation [4] */
                 double *left, /* left endpoints of the set in increasing order [num] */
                 double *right, /* right endpoints of the set in increasing order [num] */
                 double *root, /* roots of the rational function [n] */
                 double *pole, /* poles of the rational function [n] */
                 double *ext, /* on output, local extrema of the rational function [n+1] */
                 double *res) /* on output, absolute log at local extrema [n+1] */
{
    int i, loc, lambda_flip = 0;

    /* temporarily flip Mobius transformation, roots, & poles for [-lambda,-1] domain */
    if(lambda < 0.0)
    {
        lambda_flip = 1; lambda = -lambda;
        map[0] = -map[0]; map[2] = -map[2];
        for(i=0 ; i<n ; i++)
        { root[i] = -root[i]; pole[i] = -pole[i]; }
    }

    ext[0] = lambda; res[0] = log(fabs(rational(n, lambda, root, pole)));
    ext[n] = 1.0; res[n] = log(fabs(rational(n, 1.0, root, pole)));

    for(i=1 ; i<n ; i++)
    {
        /* unconstrained local extremum */
        ext[i] = local_extremum(n, root[i-1], root[i], root, pole);

        /* apply set constraints to extremum */
        loc = locate(mobius(ext[i],map), num, left, right);
        if(loc < 0)
        {
            double ext1 = mobius_inv(right[-loc-1],map), ext2 = mobius_inv(left[-loc],map);
            double val1 = -INFINITY, val2 = -INFINITY;
            if(ext1 >= root[i-1] && ext1 <= root[i])
            { val1 = log(fabs(rational(n, ext1, root, pole))); }
            if(ext2 >= root[i-1] && ext2 <= root[i])
            { val2 = log(fabs(rational(n, ext2, root, pole))); }
            if(val1 >= val2)
            { ext[i] = ext1; res[i] = val1; }
            else
            { ext[i] = ext2; res[i] = val2; }
        }
        else
        { res[i] = log(fabs(rational(n,ext[i],root,pole))); }
    }

    /* revert the flipped Mobius transformation, roots, & poles for [-lambda,-1] domain */
    if(lambda_flip)
    {
        map[0] = -map[0]; map[2] = -map[2];
        for(i=0 ; i<n ; i++)
        { root[i] = -root[i]; pole[i] = -pole[i]; }
        for(i=0 ; i<n+1 ; i++)
        { ext[i] = -ext[i]; }
    }
}

/* weights for the linearized solution updates */
void solution_weight(int n, /* number of roots/poles of the rational function */
                     double *root, /* roots of the rational function [n] */
                     double *pole, /* poles of the rational function [n] */
                     double *ext1, /* locations of extrema that interleave roots [n+1] */
                     double *ext2, /* locations of extrema that interleave poles [n+1] */
                     double *pre1, /* 1st prefactor [n+1] */
                     double *pre2, /* 2nd prefactor [n+1] */
                     double *post1, /* 1st postfactor [n] */
                     double *post2) /* 2nd postfactor [n] */
{
    int i, j;

    /* calculate weights that appear in the Cauchy kernel summation */
    for(i=0 ; i<n+1 ; i++)
    {
        pre1[i] = pre2[i] = 1.0;
        for(j=0 ; j<n ; j++)
        {
            pre1[i] *= (ext1[i] - pole[j])*(ext1[i] - root[j])/((ext1[i] - ext2[j])*(ext1[i] - ext1[j+(j>=i)]));
            pre2[i] *= (root[j] - ext2[i])*(pole[j] - ext2[i])/((ext1[j] - ext2[i])*(ext2[j+(j>=i)] - ext2[i]));
        }
        pre1[i] /= ext1[i] - ext2[n];
        pre2[i] /= ext1[n] - ext2[i];
    }

    /* calculate the prefactor weights on the root & pole updates */
    for(i=0 ; i<n ; i++)
    {
        post1[i] = (ext2[0] - root[i])*(ext1[0] - root[i]);
        post2[i] = (pole[i] - ext1[0])*(pole[i] - ext2[0]);
        for(j=0 ; j<n-1 ; j++)
        {
            post1[i] *= (ext2[j+1] - root[i])*(ext1[j+1] - root[i])/((pole[j] - root[i])*(root[j+(j>=i)] - root[i]));
            post2[i] *= (pole[i] - ext1[j+1])*(pole[i] - ext2[j+1])/((pole[i] - root[j])*(pole[i] - pole[j+(j>=i)]));
        }
        post1[i] *= (ext2[n] - root[i])*(ext1[n] - root[i])/(pole[n-1] - root[i]);
        post2[i] *= (pole[i] - ext1[n])*(pole[i] - ext2[n])/(pole[i] - root[n-1]);
    }
}

/* calculate a solution update given the existing solution & pre/post-factors */
void solution_update(int n, /* number of roots/poles of the rational function */
                     double *root, /* roots of the rational function [n] */
                     double *pole, /* poles of the rational function [n] */
                     double *ext1, /* locations of extrema that interleave roots [n+1] */
                     double *ext2, /* locations of extrema that interleave poles [n+1] */
                     double *res1, /* absolute log of the residual error at extrema that interleave roots [n+1] */
                     double *res2, /* absolute log of the residual error at extrema that interleave poles [n+1] */
                     double *error, /* error equioscillation value [1] */
                     double *scale, /* rational function scale factor [1] */
                     double *droot, /* search direction for roots [n] */
                     double *dpole, /* search direction for poles [n] */
                     double *pre1, /* 1st prefactor [n+1] */
                     double *pre2, /* 2nd prefactor [n+1] */
                     double *post1, /* 1st postfactor [n] */
                     double *post2) /* 2nd postfactor [n] */
{
    int i, j;
    double denominator = 0.0;

    /* calculate max_error updates */
    *error = 0.0;
    for(i=0 ; i<n+1 ; i++)
    {
        *error += pre1[i]*res1[i] + pre2[i]*res2[i];
        denominator += pre1[i] + pre2[i];
    }
    *error /= denominator;

    /* calculate scale update */
    *scale = 0.0;
    for(i=0 ; i<n+1 ; i++)
    { *scale += ext1[i]*(*error - res1[i])*pre1[i] + ext2[i]*(*error - res2[i])*pre2[i]; }

    /* calculate root & pole updates */
    for(i=0 ; i<n ; i++)
    {
        droot[i] = 0.0;
        dpole[i] = 0.0;

        for(j=0 ; j<n+1 ; j++)
        {
            droot[i] += pre1[j]*(*error - res1[j])/(root[i] - ext1[j]) + pre2[j]*(*error - res2[j])/(root[i] - ext2[j]);
            dpole[i] += pre1[j]*(*error - res1[j])/(pole[i] - ext1[j]) + pre2[j]*(*error - res2[j])/(pole[i] - ext2[j]);
        }

        droot[i] *= post1[i];
        dpole[i] *= post2[i];
    }

    /* switch from logarithms to values */
    *scale = exp(*scale);
    *error = exp(2.0*(*error));
}

/* objective function for the line search */
double step_objective(double step, /* step weight in [0,1] */
                      int n, /* number of roots/poles of the rational function */
                      double *error, /* overall maximum error of the rational function [1] */
                      double *scale, /* scale factor of the rational function [1] */
                      double *root, /* roots of the rational function [n] */
                      double *pole, /* poles of the rational function [n] */
                      double *ext1, /* locations of extrema that interleave roots [n+1] */
                      double *ext2, /* locations of extrema that interleave poles [n+1] */
                      double *res1, /* absolute log of the residual error at extrema that interleave roots [n+1] */
                      double *res2, /* absolute lof of the residual error at extrema that interleave poles [n+1] */
                      double *droot, /* search direction for roots [n] */
                      double *dpole, /* search direction for poles [n] */
                      double *root2, /* workspace to avoid overwriting root [n] */
                      double *pole2) /* workspace to avoid overwriting pole [n] */
{
    int i;
    double min1, min2, max1, max2;

    /* construct new solution */
    for(i=0 ; i<n ; i++)
    {
        double z = log(root[i] - ext1[i]) - log(ext1[i+1] - root[i]);
        double dz = droot[i]*(1.0/(root[i] - ext1[i]) + 1.0/(ext1[i+1] - root[i]));
        root2[i] = (ext1[i] + exp(z + step*dz)*ext1[i+1])/(1.0 + exp(z + step*dz));

        z = log(pole[i] - ext2[i+1]) - log(ext2[i] - pole[i]);
        dz = dpole[i]*(1.0/(pole[i] - ext2[i+1]) + 1.0/(ext2[i] - pole[i]));
        pole2[i] = (ext2[i+1] + exp(z + step*dz)*ext2[i])/(1.0 + exp(z + step*dz));
    }

    /* calculate new maximum error */
    for(i=0 ; i<n+1 ; i++)
    {
        res1[i] = log(fabs(rational(n,ext1[i],root2,pole2)));
        res2[i] = log(fabs(rational(n,ext2[i],pole2,root2)));
    }
    min1 = res1[0]; min2 = res2[0]; max1 = res1[0]; max2 = res2[0];
    for(i=1 ; i<n+1 ; i++)
    {
        if(min1 > res1[i]) { min1 = res1[i]; }
        if(min2 > res2[i]) { min2 = res2[i]; }
        if(max1 < res1[i]) { max1 = res1[i]; }
        if(max2 < res2[i]) { max2 = res2[i]; }
    }
    *error = exp(max1 + max2);
    *scale = exp(0.5*(max2 - max1));
    if(max1 - min1 < max2 - min2)
    { return max2 - min2; }
    return max1 - min1;
}

/* perform a golden section search in the linear search direction that reduces equioscillation errors */
/* this implementation draws heavily from [https://en.wikipedia.org/wiki/Golden-section_search] */
double safe_step(int n, /* number of roots/poles of the rational function */
                 double *error, /* overall maximum error of the rational function [1] */
                 double *scale, /* scale factor of the rational function [1] */
                 double *root, /* roots of the rational function [n] */
                 double *pole, /* poles of the rational function [n] */
                 double *ext1, /* locations of extrema that interleave roots [n+1] */
                 double *ext2, /* locations of extrema that interleave poles [n+1] */
                 double *res1, /* absolute log of the residual error at extrema that interleave roots [n+1] */
                 double *res2, /* absolute lof of the residual error at extrema that interleave poles [n+1] */
                 double *droot, /* search direction for roots [n] */
                 double *dpole, /* search direction for poles [n] */
                 double *root2, /* workspace to avoid overwriting root [n] */
                 double *pole2, /* workspace to avoid overwriting pole [n] */
                 int *info) /* on output, status of the calculation [1] */
/* RETURN: amount of reduction in the equioscillation error */
{
    int i;
    double min1, min2, max1, max2, old_min, new_min, a, b, c, d, fc, fd, gap, invphi, invphi2, max_step;
    invphi = 0.5*sqrt(5.0) - 0.5;
    invphi2 = 1.5 - 0.5*sqrt(5.0);

    /* adjust max_step to avoid root/pole collisions (broken search direction) */
    max_step = 1.0;
    for(i=0 ; i<n ; i++)
    {
        double z = log(root[i] - ext1[i]) - log(ext1[i+1] - root[i]);
        double dz = droot[i]*(1.0/(root[i] - ext1[i]) + 1.0/(ext1[i+1] - root[i]));
        if(z > STEP_TOL) { *info = 4; return 0.0; }
        if(z + max_step*dz > STEP_TOL)
        { max_step = (STEP_TOL-z)/dz; }
        if(z < -STEP_TOL) { *info = 4; return 0.0; }
        if(z + max_step*dz < -STEP_TOL)
        { max_step = (-STEP_TOL-z)/dz; }

        z = log(pole[i] - ext2[i+1]) - log(ext2[i] - pole[i]);
        dz = dpole[i]*(1.0/(pole[i] - ext2[i+1]) + 1.0/(ext2[i] - pole[i]));
        if(z > STEP_TOL) { *info = 4; return 0.0; }
        if(z + max_step*dz > STEP_TOL)
        { max_step = (STEP_TOL-z)/dz; }
        if(z < -STEP_TOL) { *info = 4; return 0.0; }
        if(z + max_step*dz < -STEP_TOL)
        { max_step = (-STEP_TOL-z)/dz; }
    }

    /* calculate initial equioscllation error */
    min1 = res1[0]; min2 = res2[0]; max1 = res1[0]; max2 = res2[0];
    for(i=1 ; i<n+1 ; i++)
    {
        if(min1 > res1[i]) { min1 = res1[i]; }
        if(min2 > res2[i]) { min2 = res2[i]; }
        if(max1 < res1[i]) { max1 = res1[i]; }
        if(max2 < res2[i]) { max2 = res2[i]; }
    }
    *error = exp(max1 + max2);
    *scale = exp(0.5*(max2 - max1));
    old_min = max1 - min1;
    if(max1 - min1 < max2 - min2)
    { old_min = max2 - min2; }

    /* perform a golden section search */
    a = 0.0;
    b = max_step;
    gap = max_step;
    c = a + invphi2*gap;
    d = a + invphi*gap;
    fc = step_objective(c, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2);
    fd = step_objective(d, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2);
    do
    {
        gap *= invphi;
        if(fc < fd)
        {
            b = d;
            d = c;
            fd = fc;
            c = a + invphi2*gap;
            fc = step_objective(c, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2);
        }
        else
        {
            a = c;
            c = d;
            fc = fd;
            d = a + invphi*gap;
            fd = step_objective(d, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2);
        }
    } while(gap > GOLDEN_TOL*max_step);

    /* update roots & poles for the new solution that are consistent w/ scale & error */
    if(fc < fd)
    { new_min = step_objective(d, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2); }
    else
    { new_min = step_objective(b, n, error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2); }
    for(i=0 ; i<n ; i++)
    {
        root[i] = root2[i];
        pole[i] = pole2[i];
    }

    *info = 0;
    return old_min - new_min;
}

/* main solver loop for computing numerical solutions for Zolotarev numbers */
double zolotarev_solve(int n, /* order of the Zolotarev number */
                       int num1, /* number of intervals in the 1st set */
                       int num2, /* number of intervals in the 2nd set */
                       double lambda, /* lambda value of the Mobius transformation */
                       double *map, /* mapping coefficients of the Mobius transformation [4] */
                       double *left1, /* left endpoints of the 1st set in increasing order [num1] */
                       double *left2, /* left endpoints of the 2nd set in increasing order [num2] */
                       double *right1, /* right endpoints of the 1st set in increasing order [num1] */
                       double *right2, /* right endpoints of the 2nd set in increasing order [num2] */
                       double *root, /* trial roots of the rational function [n] */
                       double *pole, /* trial poles of the optimal rational function [n] */
                       double *scale, /* on output, prefactor of the optimal rational function [1] */
                       int *info) /* on output, status of the calculation [1] */
/* RETURN: value of the Zolotarev number for the numerical solution */
{
    int iter = 0;
    double *ext1, *ext2, *res1, *res2, *pre1, *pre2, *post1, *post2, *droot, *dpole, *root2, *pole2, error, progress = 1.0;
    ext1 = (double*)malloc(sizeof(double)*(n+1));
    ext2 = (double*)malloc(sizeof(double)*(n+1));
    res1 = (double*)malloc(sizeof(double)*(n+1));
    res2 = (double*)malloc(sizeof(double)*(n+1));
    pre1 = (double*)malloc(sizeof(double)*(n+1));
    pre2 = (double*)malloc(sizeof(double)*(n+1));
    post1 = (double*)malloc(sizeof(double)*n);
    post2 = (double*)malloc(sizeof(double)*n);
    droot = (double*)malloc(sizeof(double)*n);
    dpole = (double*)malloc(sizeof(double)*n);
    root2 = (double*)malloc(sizeof(double)*n);
    pole2 = (double*)malloc(sizeof(double)*n);
    *info = 0;

    while(progress > 0.0 && ++iter < MAX_ITER)
    {
        /* calculate new local extrema in both domains */
        all_extrema(n, num1, lambda, map, left1, right1, root, pole, ext1, res1);
        all_extrema(n, num2, -lambda, map, left2, right2, pole, root, ext2, res2);

        /* calculate a search direction */
        solution_weight(n, root, pole, ext1, ext2, pre1, pre2, post1, post2);
        solution_update(n, root, pole, ext1, ext2, res1, res2, &error, scale, droot, dpole, pre1, pre2, post1, post2);

        /* take a safe step in the search direction to improve equioscillation */
        progress = safe_step(n, &error, scale, root, pole, ext1, ext2, res1, res2, droot, dpole, root2, pole2, info);
        if(*info != 0) { break; }
    }
    if(iter == MAX_ITER)
    { *info = 5; }

    free(pole2);
    free(root2);
    free(dpole);
    free(droot);
    free(post2);
    free(post1);
    free(pre2);
    free(pre1);
    free(res2);
    free(res1);
    free(ext2);
    free(ext1);
    return error;
}

/* condition number function */
double cofunc(int n, /* number of roots/poles of the rational function */
              double z, /* point at which the rational function is evaluated */
              double lambda, /* edge of approximation domain, [lambda, 1] */
              double *root, /* roots of the rational function [n] */
              double *pole, /* poles of the rational function [n] */
              double *pre) /* precomputed coefficients of the weighted Lagrange polynomials [n] */
/* RETURN: value of the condition number function */
{
    int i;
    double ans = 0.0;

    for(i=0 ; i<n ; i++)
    {
        double opt = (z < root[i]) ? 1.0 : lambda;
        if(z == root[i]) { return 1.0; }
        ans += fabs(pre[i]*(z + opt)/((root[i] + opt)*(z - root[i])));
    }
    ans *= fabs(rational(n, z, root, pole));
    return ans;
}

/* 1st & 2nd logarithmic derivatives of the condition number function */
void dlog_cofunc(int n, /* number of roots/poles of the rational function */
                 double z, /* point at which the rational function is evaluated */
                 double lambda, /* edge of approximation domain, [lambda, 1] */
                 double *root, /* roots of the rational function [n] */
                 double *pole, /* poles of the rational function [n] */
                 double *pre, /* precomputed coefficients of the weighted Lagrange polynomials [n] */
                 double *deriv) /* 1st & 2nd logarithmic derivatives on output [2] */
{
    int i;
    double sum = 0.0, dlog1 = 0.0, dlog2 = 0.0;

    dlog_rational(n, z, root, pole, deriv);
    for(i=0 ; i<n ; i++)
    {
        double opt = (z < root[i]) ? 1.0 : lambda;
        double val = fabs(pre[i]*(z + opt)/((root[i] + opt)*(z - root[i])));
        sum += val;
        val *= 1.0/(z + opt) - 1.0/(z - root[i]);
        dlog1 += val;
        val *= -2.0/(z - root[i]);
        dlog2 += val;
    }
    deriv[0] += dlog1/sum;
    deriv[1] += dlog2/sum - dlog1*dlog1/(sum*sum);
}

/* find a local extrema of the condition number function using Newton's method w/ bisection failsafe */
double local_condition(int n, /* number of roots/poles of the rational function */
                       double left, /* left edge of search interval */
                       double right, /* right edge of search interval */
                       double lambda, /* lambda value of the Mobius transformation */
                       double *root, /* roots of the rational function [n] */
                       double *pole, /* poles of the rational function [n] */
                       double *pre) /* precomputed coefficients of the weighted Lagrange polynomials [n] */
/* RETURN: location of the local extrema of the condition number function */
{
    int iter = 0, not_converged = 1, almost_converged = 0;
    double deriv[2], guess = 0.5*(left+right), dguess = left-right;

    while(not_converged)
    {
        /* Newton update w/ bisection failsafe */
        if(guess + dguess <= left || guess + dguess >= right)
        { guess = 0.5*(left + right); }
        else
        { guess += dguess; }

        /* update function value */
        dlog_cofunc(n, guess, lambda, root, pole, pre, deriv);
        dguess = deriv[0]/fabs(deriv[1]);
        if(dguess > 0.0) { left = guess; }
        else { right = guess; }

        /* convergence criteria */
        if(almost_converged)
        { not_converged = 0; }
        if(fabs(dguess) < NEWTON_TOL*fabs(guess))
        { almost_converged = 1; }
        if(++iter == MAX_ITER_ROOT)
        { printf("ERROR: maximum iteration exceeded in local_condition\n"); exit(1); }
    }
    return guess;
}

/* calculate the condition number */
double condition_number(int n, /* number of roots/poles of the rational function */
                        int num, /* number of intervals in the approximation domain */
                        double lambda, /* lambda value of the Mobius transformation, negative sign denotes [-lambda,-1] domain */
                        double *map, /* mapping coefficients of Mobius transformation [4] */
                        double *root, /* roots of the rational function [n] */
                        double *pole, /* poles of the rational function [n] */
                        double *left, /* left endpoints of intervals in the approximation domain [num] */
                        double *right) /* left endpoints of intervals in the approximation domain [num] */
/* RETURN: value of the condition number */
{
    int i, j, lambda_flip = 0;
    double max_condition, new_condition, *pre;
    pre = (double*)malloc(sizeof(double)*n);

    /* temporarily flip Mobius transformation, roots, & poles for [-lambda,-1] domain */
    if(lambda < 0.0)
    {
        lambda_flip = 1; lambda = -lambda;
        map[0] = -map[0]; map[2] = -map[2];
        for(i=0 ; i<n ; i++)
        { root[i] = -root[i]; pole[i] = -pole[i]; }
    }

    /* precompute the coefficients of the weighted Langrange polynomials */
    for(i=0 ; i<n ; i++)
    {
        pre[i] = 1.0;
        for(j=0 ; j<n-1 ; j++)
        { pre[i] *= (root[i] - pole[j])/(root[i] - root[j+(j>=i)]); }
        pre[i] *= root[i] - pole[n-1];
    }

    /* trivial extrema at edges of approximation domain */
    max_condition = cofunc(n, lambda, lambda, root, pole, pre);
    new_condition = cofunc(n, 1.0, lambda, root, pole, pre);
    if(new_condition > max_condition)
    { max_condition = new_condition; }

    /* find internal local extrema */
    for(i=1 ; i<n ; i++)
    {
        int loc;
        double ext;

        /* calculate unconstrained local extrema */
        ext = local_condition(n, root[i-1], root[i], lambda, root, pole, pre);

        /* check for constrained local extrema */
        loc = locate(mobius(ext,map), num, left, right);
        if(loc < 0)
        {
            new_condition = 1.0; /* trivial lower bound on condition number function */
            double ext1 = mobius_inv(right[-loc-1],map), ext2 = mobius_inv(left[-loc],map);
            if(ext1 >= root[i-1] && ext1 <= root[i])
            { new_condition = cofunc(n, ext1, lambda, root, pole, pre); }
            if(ext2 >= root[i-1] && ext2 <= root[i])
            {
                double right_condition = cofunc(n, ext2, lambda, root, pole, pre);
                if(right_condition > new_condition)
                { new_condition = right_condition; }
            }
        }
        else
        { new_condition = cofunc(n, ext, lambda, root, pole, pre); }

        /* update maximum */
        if(new_condition > max_condition)
        { max_condition = new_condition; }
    }

    /* revert the flipped Mobius transformation, roots, & poles for [-lambda,-1] domain */
    if(lambda_flip)
    {
        map[0] = -map[0]; map[2] = -map[2];
        for(i=0 ; i<n ; i++)
        { root[i] = -root[i]; pole[i] = -pole[i]; }
    }

    free(pre);
    return max_condition;
}

/* comparison function to sort reals using qsort */
int real_cmp(const void *r1, /* pointer to 1st real [1] */
             const void *r2) /* pointer to 2nd real [1] */
/* RETURN: valid comparison output, -1 for less than, 0 for equal to, & 1 for greater than */
{
    if(*(double*)r1 <= *(double*)r2) { return -1; }
    if(*(double*)r1 >= *(double*)r2) { return 1; }
    return 0;
}

/* interface to Zolotarev number evaluation, Z_n(X,Y) for X = Union_i[end1[i],end1[i+1]] & Y = Union_i[end2[i],end2[i+1]] */
double zolotarev_number(int n, /* order of the Zolotarev number */
                        int num1, /* number of intervals in the 1st set */
                        int num2, /* number of intervals in the 2nd set */
                        double *left1, /* left endpoints of the 1st set in increasing order [num1] */
                        double *left2, /* left endpoints of the 2nd set in increasing order [num2] */
                        double *right1, /* right endpoints of the 1st set in increasing order [num1] */
                        double *right2, /* right endpoints of the 2nd set in increasing order [num2] */
                        double *root, /* on output, roots of the optimal rational function [n] */
                        double *pole, /* on output, poles of the optimal rational function [n] */
                        double *scale, /* on output, prefactor of the optimal rational function [1] */
                        double *conum1, /* on output, condition number on the 1st set [1] */
                        double *conum2, /* on output, condition number on the 2nd set [1] */
                        int *info) /* on output, status of the calculation [1] */
{
    int i;
    double error, lambda, map[4];

    /* construct Mobius transformation & check sets for errors */
    lambda = mobius_setup(num1, num2, map, left1, left2, right1, right2, info);
    if(*info) { return 0.0; }

    /* check for trivial & analytical solutions */
    error = zolotarev_check(n, num1, num2, lambda, map, left1, left2, right1, right2, root, pole, scale, info);
    if(*info > 0) { return 0.0; }

    /* calculate numerical solution */
    if(error < 0.0)
    {
        /* construct initial guess for numerical solution */
        zolotarev_guess(n, num1, lambda, map, left1, right1, root);
        zolotarev_guess(n, num2, -lambda, map, left2, right2, pole);

        /* main solver loop */
        error = zolotarev_solve(n, num1, num2, lambda, map, left1, left2, right1, right2, root, pole, scale, info);
        if(*info) { return 0.0; }
    }

    /* compute condition numbers */
    *conum1 = condition_number(n+(*info), num1, lambda, map, root, pole, left1, right1);
    *conum2 = condition_number(n+(*info), num2, -lambda, map, pole, root, left2, right2);

    /* map roots & poles to the original domain */
    for(i=0 ; i<n+(*info) ; i++)
    {
        root[i] = mobius(root[i], map);
        pole[i] = mobius(pole[i], map);
    }
    qsort(root, n+(*info), sizeof(double), real_cmp);
    qsort(pole, n+(*info), sizeof(double), real_cmp);

    return error;
}

/* command-line interface */
int main(int argc, char **argv)
{
    int n, num1, num2, i, info;
    clock_t begin, end;
    double *left1, *left2, *right1, *right2, *root, *pole, scale, conum1, conum2, error;
    FILE *input_file;

    if(argc < 4)
    {
        printf("USAGE: <executable> <Zolotarev number order> <1st domain input file> <2nd domain input file>\n");
        return 1;
    }
    sscanf(argv[1], "%d", &n);
    root = (double*)malloc(sizeof(double)*n);
    pole = (double*)malloc(sizeof(double)*n);

    input_file = fopen(argv[2], "r");
    fscanf(input_file, "%d", &num1);
    left1 = (double*)malloc(sizeof(double)*num1);
    right1 = (double*)malloc(sizeof(double)*num1);
    for(i=0 ; i<num1 ; i++)
    { fscanf(input_file, "%lf %lf", left1+i, right1+i); }
    fclose(input_file);

    input_file = fopen(argv[3], "r");
    fscanf(input_file, "%d", &num2);
    left2 = (double*)malloc(sizeof(double)*num2);
    right2 = (double*)malloc(sizeof(double)*num2);
    for(i=0 ; i<num2 ; i++)
    { fscanf(input_file, "%lf %lf", left2+i, right2+i); }
    fclose(input_file);

    begin = clock();
    error = zolotarev_number(n, num1, num2, left1, left2, right1, right2, root, pole, &scale, &conum1, &conum2, &info);
    end = clock();

    if(info > 0)
    { printf("ERROR: info = %d\n",info); exit(1); }
    if(info < 0)
    { printf("WARNING: degenerate solution\n"); n += info; }
    printf("Z(%d) = %15.15e\n", n, error);
    printf("condition number for 1st domain = %15.15e\n", conum1);
    printf("condition number for 2nd domain = %15.15e\n", conum2);
    for(i=0 ; i<n ; i++)
    { printf("root[%d] = %15.15e\n", i, root[i]); }
    for(i=0 ; i<n ; i++)
    { printf("pole[%d] = %15.15e\n", i, pole[i]); }
    printf("time elapsed = %.5lf s\n", (double)(end-begin)/(double)CLOCKS_PER_SEC);

    free(right2);
    free(left2);
    free(right1);
    free(left1);
    free(pole);
    free(root);

    return 1;
}

