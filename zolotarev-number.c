/* Zolotarev number evaluation for finite unions of closed intervals */

/* compile into an executable as-is to use the command-line interface
   OR
   remove the main & compile into a library to use the function interface */

/* command-line interface for calculating Zolotarev numbers:
   USAGE: <executable> <Zolotarev number order> <1st domain input file> <2nd domain input file>

   input file format:
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
                        double *end1, /* ordered endpoints of intervals in the 1st set [2*num1] */
                        double *end2, /* ordered endpoints of intervals in the 2nd set [2*num2] */
                        double *root, /* roots of the optimal rational function [n] */
                        double *pole, /* poles of the optimal rational function [n] */
                        double *lebesgue); /* Lebesgue-like constants of the optimal rational function & its reciprocal [2] */
/* RETURN: value of the Zolotarev number */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

/* common but nonstandard definition of pi */
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

/* maximum number of iterations of the ascending Landen transformation needed at double precision */
#define MAX_ITER_DN 15

/* maximum number of iterations of Newton's method */
#define MAX_ITER_EXT 20

/* tolerance for Newton's method identifying the step before expected convergence */
#define EXTREMA_TOL 1e-9

/* maximum relative deviation from equioscillation (between 0 and 1) */
#define EQUIOSCILLATION_DEVIATION 0.1

/* bound on size of higher-order corrections (must be less than 1) */
#define HIGHER_ORDER_BOUND 0.9

/* fractional step reduction in the line search */
#define STEP_REDUCTION 0.5

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

/* local coordinate used to find a local extrema */
double local_map(double z, /* unbounded coordinate */
                 double left, /* left domain edge */
                 double right) /* right domain edge */
/* RETURN: bounded coordinate between left & right */
{
    if(z == 0.0)
    { return 0.5*(left+right); }
    return (1.0 + 0.5*(left+right)*z - sqrt(1.0 + 0.25*z*z*(left-right)*(left-right)))/z;
}

/* find a local extrema using Newton's method on a mapped domain */
double local_extrema(int i, /* index of the local extrema */
                     int n, /* number of roots/poles of the rational function */
                     double *root, /* roots of the rational function [n] */
                     double *pole) /* poles of the rational function [n] */
/* RETURN: location of the local extrema */
{
    int iter = 0, not_converged = 1, almost_converged = 0;
    double local = 0.0, old_mapped, mapped, deriv[2], left = root[i], right = root[i+1];

    if(left > right)
    { left = root[i+1]; right = root[i]; }
    mapped = local_map(local, left, right);

    while(not_converged)
    {
        /* update includes Jacobian of local_map */
        dlog_rational(n, mapped, root, pole, deriv);
        local += (1.0/((mapped-left)*(mapped-left))+1.0/((mapped-right)*(mapped-right)))*deriv[0]/deriv[1];

        /* store old extrema location, calculate new extrema location */
        old_mapped = mapped;
        mapped = local_map(local, left, right);

        /* convergence criteria */
        if(almost_converged)
        { not_converged = 0; }
        if(fabs(mapped-old_mapped) < EXTREMA_TOL*fabs(old_mapped))
        { almost_converged = 1; }
        if(++iter == MAX_ITER_EXT)
        { printf("ERROR: maximum iteration exceeded in local_extrema\n"); exit(1); }
    }
    return mapped;
}

/* comparison functions to test if a point is in an open or closed interval using bsearch */
int open_cmp(const void *pt, /* pointer to value being located [1] */
             const void *end) /* pointer to interval being compared with [2] */
/* RETURN: valid comparison output, -1 for less than, 0 for equal to, & 1 for greater than */
{
    if(*(double*)pt <= *(double*)end) { return -1; }
    if(*(double*)pt >= *((double*)end+1)) { return 1; }
    return 0;
}
int closed_cmp(const void *pt, /* pointer to value being located [1] */
               const void *end) /* pointer to interval being compared with [2] */
/* RETURN: valid comparison output, -1 for less than, 0 for equal to, & 1 for greater than */
{
    if(*(double*)pt < *(double*)end) { return -1; }
    if(*(double*)pt > *((double*)end+1)) { return 1; }
    return 0;
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

/* find all extrema of a rational function between its roots & in the approximation domain */
double global_extremum(int n, /* number of roots/poles of the rational function */
                       int num, /* number of intervals in the approximation domain */
                       double weight, /* weight applied to errors outside the approximation domain */
                       double *root, /* roots of the rational function [n] */
                       double *pole, /* poles of the rational function [n] */
                       double *end, /* endpoints of intervals in the approximation domain [2*num] */
                       double *map, /* Mobius transformation to the approximation domain [4] */
                       double *ext, /* locations of local extrema that interleave roots [n+1] */
                       double *val, /* values of local extrema of the rational function [n+1] */
                       int *inc) /* denotes if a local extrema is in the approximation domain [n+1] */
/* RETURN: absolute (weighted) global extremum value */
{
    int i;
    double max_val;

    /* trivial extrema at edges of approximation domain are not adjusted */
    val[0] = fabs(rational(n, ext[0], root, pole));
    val[n] = fabs(rational(n, ext[n], root, pole));
    max_val = val[0];
    if(val[n] > max_val)
    { max_val = val[n]; }

    /* find internal local extrema */
    for(i=1 ; i<n ; i++)
    {
        double left, right, left_min = root[i-1], right_max = root[i], ext_map, *left_ptr;
    
        /* swap roots if the order is reversed */
        if(left_min > right_max)
        { left_min = root[i]; right_max = root[i-1]; }

        /* calculate the local extremum between the active roots */
        ext[i] = local_extrema(i-1, n, root, pole);
        ext_map = mobius(ext[i],map);
        val[i] = fabs(rational(n, ext[i], root, pole));
        inc[i] = 1;

        /* identify the gap, if any, that contains the local extremum */
        left_ptr = bsearch(&ext_map, end+1, num, sizeof(double)*2, open_cmp); /* in stdlib.h */
        if(left_ptr != NULL)
        { left = mobius_inv(*left_ptr, map); right = mobius_inv(*(left_ptr+1), map); inc[i] = 0; }
        if(ext[i] > mobius_inv(end[2*num-1], map) && ext[i] < mobius_inv(end[0], map))
        { left = mobius_inv(end[2*num-1], map); right = mobius_inv(end[0], map); inc[i] = 0; }

        /* weight the local extrema if it is outside the approximation domain & check endpoints */
        if(inc[i] == 0)
        {
            val[i] *= weight;

            /* check left endpoint for a larger extrema */
            if(left > left_min)
            {
                double left_val = fabs(rational(n, left, root, pole));
                if(left_val > val[i])
                {
                    ext[i] = left;
                    val[i] = left_val;
                    inc[i] = 1;
                }
            }

            /* check right endpoint for a larger extrema */
            if(right < right_max)
            {
                double right_val = fabs(rational(n, right, root, pole));
                if(right_val > val[i])
                {
                    ext[i] = right;
                    val[i] = right_val;
                    inc[i] = 1;
                }
            }
        }

        /* update global maximum */
        if(val[i] > max_val)
        { max_val = val[i]; }
    }

    return max_val;
}

/* calculate the search direction via analytical solution of a linear system w/ a large Cauchy submatrix */
void search_direction(int n, /* number of roots/poles of the rational function */
                      double *root, /* roots of the rational function [n] */
                      double *pole, /* poles of the rational function [n] */
                      double *ext1, /* locations of extrema that interleave roots [n+1] */
                      double *ext2, /* locations of extrema that interleave poles [n+1] */
                      double *val1, /* extremal values of the rational function interleaving roots [n+1] */
                      double *val2, /* extremal values of the rational function interleaving poles [n+1] */
                      double *droot, /* search direction for roots [n] */
                      double *dpole, /* search direction for poles [n] */
                      double *work) /* local workspace [2*n+2] */
{
    int i, j;
    double *w1 = work, *w2 = work+n+1, min_val1 = val1[0], min_val2 = val2[0], sum1 = 0.0, sum2 = 0.0, ratio;

    /* find minimum values for reweighting */
    for(i=1 ; i<n+1 ; i++)
    {
        if(val1[i] < min_val1)
        { min_val1 = val1[i]; }
        if(val2[i] < min_val2)
        { min_val2 = val2[i]; }
    }

    /* calculate weights that appear in the Cauchy kernel summation */
    for(i=0 ; i<n+1 ; i++)
    {
        w1[i] = w2[i] = 1.0;
        for(j=0 ; j<n ; j++)
        {
            w1[i] *= (ext1[i] - pole[j])*(ext1[i] - root[j])/((ext1[i] - ext2[j])*(ext1[i] - ext1[j+(j>=i)]));
            w2[i] *= (root[j] - ext2[i])*(pole[j] - ext2[i])/((ext1[j] - ext2[i])*(ext2[j+(j>=i)] - ext2[i]));
        }
        w1[i] /= ext1[i] - ext2[n];
        w2[i] /= ext1[n] - ext2[i];
    }

    /* calculate the important sums & update the weights */
    for(i=0 ; i<n+1 ; i++)
    {
        sum1 += w1[i] + w2[i];
        sum2 += w1[i]*min_val1/val1[i] + w2[i]*min_val2/val2[i];
    }
    ratio = sum1/sum2;
    for(i=0 ; i<n+1 ; i++)
    {
        w1[i] *= (1.0 - ratio*min_val1/val1[i]);
        w2[i] *= (1.0 - ratio*min_val2/val2[i]);
    }

    /* calculate the Cauchy kernel summation */
    for(i=0 ; i<n ; i++)
    {
        droot[i] = dpole[i] = 0.0;
        for(j=0 ; j<n+1 ; j++)
        {
            droot[i] += w1[j]/(root[i] - ext1[j]) + w2[j]/(root[i] - ext2[j]);
            dpole[i] += w1[j]/(pole[i] - ext1[j]) + w2[j]/(pole[i] - ext2[j]);
        }
    }

    /* calculate the prefactor weights */
    for(i=0 ; i<n ; i++)
    {
        droot[i] *= (root[i] - ext2[0])*(root[i] - ext1[0]);
        dpole[i] *= (ext1[0] - pole[i])*(ext2[0] - pole[i]);
        for(j=0 ; j<n-1 ; j++)
        {
            droot[i] *= (root[i] - ext2[j+1])*(root[i] - ext1[j+1])/((root[i] - pole[j])*(root[i] - root[j+(j>=i)]));
            dpole[i] *= (ext1[j+1] - pole[i])*(ext2[j+1] - pole[i])/((root[j] - pole[i])*(pole[j+(j>=i)] - pole[i]));
        }
        droot[i] *= (root[i] - ext2[n])*(root[i] - ext1[n])/(root[i] - pole[n-1]);
        dpole[i] *= (ext1[n] - pole[i])*(ext2[n] - pole[i])/(root[n-1] - pole[i]);
    }
}

/* Lebesgue-like function that comes from the error analysis
   NOTE: this function is not invariant to Mobius transformations & has a transformation-dependent correction */
double lebesgue(int n, /* number of roots/poles of the rational function */
                double z, /* point at which the rational function is evaluated */
                double *root, /* roots of the rational function [n] */
                double *pole, /* poles of the rational function [n] */
                double *res, /* residues & their weighted sum [n+1] */
                double *map) /* Mobius transformation to the approximation domain [4] */
/* RETURN: value of the function */
{
    int i;
    double ans = res[n];

    for(i=0 ; i<n ; i++)
    { ans += fabs(res[i]*(map[2]*z + map[3])/((map[2]*root[i] + map[3])*(z - root[i]))); }
    ans *= fabs(rational(n, z, root, pole));
    return ans;
}

/* 1st & 2nd logarithmic derivatives of the Lebesgue-like function that comes from the error analysis
   NOTE: this function is not invariant to Mobius transformations & has a transformation-dependent correction */
void dlog_lebesgue(int n, /* number of roots/poles of the rational function */
               double z, /* point at which the rational function is evaluated */
               double *root, /* roots of the rational function [n] */
               double *pole, /* poles of the rational function [n] */
               double *res, /* residues & their weighted sum [n+1] */
               double *map, /* Mobius transformation to the approximation domain [4] */
               double *deriv) /* 1st & 2nd logarithmic derivatives on output [2] */
{
    int i;
    double sum = res[n], dlog1 = 0.0, dlog2 = 0.0;

    dlog_rational(n, z, root, pole, deriv);
    for(i=0 ; i<n ; i++)
    {
        double val = fabs(res[i]*(map[2]*z + map[3])/((map[2]*root[i] + map[3])*(z - root[i])));
        sum += val;
        val *= map[2]/(map[2]*z + map[3]) - 1.0/(z - root[i]);
        dlog1 += val;
        val *= -2.0/(z - root[i]);
        dlog2 += val;
    }
    deriv[0] += dlog1/sum;
    deriv[1] += dlog2/sum - dlog1*dlog1/(sum*sum);
}

/* find a local extrema of the Lebesgue-like function using Newton's method on a mapped domain
  NOTE: this process assumes that there is only one local extrema between each pair of roots,
        which is observed in practice but is as-yet unproven  */
double local_lebesgue(int i, /* index of the local extrema */
                      int n, /* number of roots/poles of the rational function */
                      double *root, /* roots of the rational function [n] */
                      double *pole, /* poles of the rational function [n] */
                      double *res, /* residues & their weighted sum [n+1] */
                      double *map) /* Mobius transformation to the approximation domain [4] */
/* RETURN: location of the local extrema of the Lebesgue-like function */
{
    int iter = 0, not_converged = 1, almost_converged = 0;
    double local = 0.0, old_mapped, mapped, deriv[2], left = root[i], right = root[i+1];

    if(left > right)
    { left = root[i+1]; right = root[i]; }
    mapped = local_map(local, left, right);

    while(not_converged)
    {
        /* update includes Jacobian of local_map */
        dlog_lebesgue(n, mapped, root, pole, res, map, deriv);
        local += (1.0/((mapped-left)*(mapped-left))+1.0/((mapped-right)*(mapped-right)))*deriv[0]/deriv[1];

        /* store old extrema location, calculate new extrema location */
        old_mapped = mapped;
        mapped = local_map(local, left, right);

        /* convergence criteria */
        if(almost_converged)
        { not_converged = 0; }
        if(fabs(mapped-old_mapped) < EXTREMA_TOL*fabs(old_mapped))
        { almost_converged = 1; }
        if(++iter == MAX_ITER_EXT)
        { printf("ERROR: maximum iteration exceeded in local_lebesgue\n"); exit(1); }
    }
    return mapped;
}

/* search for the maximum of the Lebesgue-like function */
double global_lebesgue(int n, /* number of roots/poles of the rational function */
                       int num, /* number of intervals in the approximation domain */
                       double *root, /* roots of the rational function [n] */
                       double *pole, /* poles of the rational function [n] */
                       double *end, /* endpoints of intervals in the approximation domain [2*num] */
                       double *map, /* Mobius transformation to the approximation domain [4] */
                       double *ext, /* locations of local extrema that interleave roots [n+1] */
                       double *val, /* values of local extrema of the Lebesgue-like function [n+1] */
                       int *inc, /* denotes if a local extrema is in the approximation domain [n+1] */
                       double *work) /* local workspace [n+1] */
/* RETURN: value of the Lebesgue-like constant */
{
    int i, j;
    double max_val, *res = work, alt_res = 0.0;

    /* calculate the residues & weights needed to evaluate the Lebesgue-like function */
    for(i=0 ; i<n ; i++)
    {
        res[i] = 1.0;
        for(j=0 ; j<n-1 ; j++)
        { res[i] *= (root[i] - pole[j])/(root[i] - root[j+(j>=i)]); }
        res[i] *= root[i] - pole[n-1];
    }
    res[n] = 0.0;
    for(i=0 ; i<n ; i++)
    {
        res[n] += fabs(res[i]*(map[3] - map[2]*ext[0])/((map[3] + map[2]*root[i])*(ext[0] + root[i])));
        alt_res += fabs(res[i]*(map[3] - map[2]*ext[n])/((map[3] + map[2]*root[i])*(ext[n] + root[i])));
    }
    if(alt_res > res[n])
    { res[n] = alt_res; }

    /* trivial extrema at edges of approximation domain are not adjusted */
    val[0] = lebesgue(n, ext[0], root, pole, res, map);
    val[n] = lebesgue(n, ext[n], root, pole, res, map);
    max_val = val[0];
    if(val[n] > max_val)
    { max_val = val[n]; }

    /* find internal local extrema */
    for(i=1 ; i<n ; i++)
    {
        double left, right, left_min = root[i-1], right_max = root[i], ext_map, *left_ptr;
    
        /* swap roots if the order is reversed */
        if(left_min > right_max)
        { left_min = root[i]; right_max = root[i-1]; }

        /* calculate the local extremum between the active roots */
        ext[i] = local_lebesgue(i-1, n, root, pole, res, map);
        ext_map = mobius(ext[i],map);
        val[i] = lebesgue(n, ext[i], root, pole, res, map);
        inc[i] = 1;

        /* identify the gap, if any, that contains the local extremum */
        left_ptr = bsearch(&ext_map, end+1, num, sizeof(double)*2, open_cmp); /* in stdlib.h */
        if(left_ptr != NULL)
        { left = mobius_inv(*left_ptr, map); right = mobius_inv(*(left_ptr+1), map); inc[i] = 0; }
        if(ext[i] > mobius_inv(end[2*num-1], map) && ext[i] < mobius_inv(end[0], map))
        { left = mobius_inv(end[2*num-1], map); right = mobius_inv(end[0], map); inc[i] = 0; }

        /* weight the local extrema if it is outside the approximation domain & check endpoints */
        if(inc[i] == 0)
        {
            val[i] = 0.0;

            /* check left endpoint for a larger extrema */
            if(left > left_min)
            {
                double left_val = lebesgue(n, left, root, pole, res, map);
                if(left_val > val[i])
                {
                    ext[i] = left;
                    val[i] = left_val;
                    inc[i] = 1;
                }
            }

            /* check right endpoint for a larger extrema */
            if(right < right_max)
            {
                double right_val = lebesgue(n, right, root, pole, res, map);
                if(right_val > val[i])
                {
                    ext[i] = right;
                    val[i] = right_val;
                    inc[i] = 1;
                }
            }
        }

        /* update global maximum */
        if(val[i] > max_val)
        { max_val = val[i]; }
    }

    return max_val;
}

/* comparison function to sort poles using qsort */
int pole_cmp(const void *pole1, /* pointer to 1st pole [1] */
             const void *pole2) /* pointer to 2nd pole [1] */
/* RETURN: valid comparison output, -1 for less than, 0 for equal to, & 1 for greater than */
{
    if(*(double*)pole1 <= *(double*)pole2) { return -1; }
    if(*(double*)pole1 >= *(double*)pole2) { return 1; }
    return 0;
}

/* interface to Zolotarev number evaluation, Z_n(X,Y) for X = Union_i[end1[i],end1[i+1]] & Y = Union_i[end2[i],end2[i+1]]
   NOTE: Y must be partitionable into Y_+ U Y_- such that Y_+ > X > Y_-
   NOTE: floating-point +/- INFINITY is supported for the 1st & last endpoints of Y (end2[0] & end2[2*num2-1]) */
double zolotarev_number(int n, /* order of the Zolotarev number */
                        int num1, /* number of intervals in the 1st set */
                        int num2, /* number of intervals in the 2nd set */
                        double *end1, /* ordered endpoints of intervals in the 1st set [2*num1] */
                        double *end2, /* ordered endpoints of intervals in the 2nd set [2*num2] */
                        double *root, /* roots of the optimal rational function [n] */
                        double *pole, /* poles of the optimal rational function [n] */
                        double *lebesgue) /* Lebesgue-like constants of the optimal rational function & its reciprocal [2] */
/* RETURN: value of the Zolotarev number */
{
    int i, numerical_solution = 0;
    double *ymin_ptr, *ymax_ptr, xmin, xmax, ymin, ymax, lambda, map[4], Kp, max_error;

    /* allocate workspaces for extrema locations & values */
    int *inc1 = (int*)malloc(sizeof(int)*(n+1));
    int *inc2 = (int*)malloc(sizeof(int)*(n+1));
    double *ext1 = (double*)malloc(sizeof(double)*(n+1));
    double *ext2 = (double*)malloc(sizeof(double)*(n+1));
    double *val1 = (double*)malloc(sizeof(double)*(n+1));
    double *val2 = (double*)malloc(sizeof(double)*(n+1));
    double *work = (double*)malloc(sizeof(double)*2*(n+1));

    /* calculate the Mobius transformation to/from the standard domain, z |-> (map[0]*z + map[1])/(map[2]*z + map[3]) */
    ymax_ptr = bsearch(end1, end2+1, num2, sizeof(double)*2, open_cmp); /* in stdlib.h */
    if(ymax_ptr == NULL)
    {
        ymin_ptr = end2;
        ymax_ptr = end2 + 2*num2 - 1;
    }
    else
    { ymin_ptr = ymax_ptr + 1; }
    xmin = end1[0];
    xmax = end1[2*num1-1];
    ymin = *ymin_ptr;
    ymax = *ymax_ptr;
    lambda = sqrt(fabs((xmax-xmin)*(ymax-ymin))) - sqrt(fabs((xmax-ymax)*(xmin-ymin)));
    lambda = lambda*lambda/fabs((xmin-ymax)*(xmax-ymin));
    map[0] = -(1.0-lambda)*xmin*xmax + (1.0+lambda)*ymax*xmax - 2.0*lambda*ymax*xmin;
    map[1] = -(1.0-lambda)*lambda*xmin*xmax - (1.0+lambda)*lambda*ymax*xmax + 2.0*lambda*ymax*xmin;
    map[2] = (1.0-lambda)*ymax - (1.0+lambda)*xmin + 2.0*lambda*xmax;
    map[3] = (1.0-lambda)*lambda*ymax + (1.0+lambda)*lambda*xmin - 2.0*lambda*xmax;

    /* assign trivial extrema at edges of the mapped approximation domain */
    ext1[0] = lambda;
    ext1[n] = 1.0;
    ext2[0] = -lambda;
    ext2[n] = -1.0;
    inc1[0] = inc1[n] = inc2[0] = inc2[n] = 1;

    /* calculate the roots, poles, & error of the analytical solution for num1 = num2 = 1 */
    Kp = elliptic_K(lambda);
    max_error = 1.0;
    for(i=0 ; i<n ; i++)
    {
        root[i] = elliptic_dn(Kp*(1.0 - ((double)i+0.5)/(double)n),lambda);
        pole[i] = -root[i];
        max_error *= ((1.0 - root[i])*(1.0 - root[i]))/((1.0 + root[i])*(1.0 - root[i]));
    }

    /* check if analytical solution is valid */
    for(i=1 ; i<n ; i++)
    {
        double mid = elliptic_dn(Kp*(double)i/(double)n,lambda);
        double mid1 = mobius(mid, map), mid2 = mobius(-mid, map);
        double *loc1 = bsearch(&mid1, end1, num1, sizeof(double)*2, closed_cmp); /* in stdlib.h */
        double *loc2 = bsearch(&mid2, end2, num2, sizeof(double)*2, closed_cmp); /* in stdlib.h */

        if(loc1 == NULL || loc2 == NULL)
        { numerical_solution = 1; }
    }

    /* calculate numerical solution if the analytical solution is not valid */
    if(numerical_solution)
    {
        int progress = 1, instability = 1;
        double old_max_error, error1, error2, min_error1, min_error2, max_length, weight;

        /* allocate workspaces for linear search directions */
        double *droot = (double*)malloc(sizeof(double)*n);
        double *dpole = (double*)malloc(sizeof(double)*n);
        double *root2 = (double*)malloc(sizeof(double)*n);
        double *pole2 = (double*)malloc(sizeof(double)*n);

        /* calculate the initial maximum error */
        weight = EQUIOSCILLATION_DEVIATION;
        error1 = global_extremum(n, num1, weight, root, pole, end1, map, ext1, val1, inc1);
        error2 = global_extremum(n, num2, weight, pole, root, end2, map, ext2, val2, inc2);
        old_max_error = error1*error2;

        /* main iterative loop */
        while(progress || instability)
        {
            /* calculate an initial search direction */
            search_direction(n, root, pole, ext1, ext2, val1, val2, droot, dpole, work);

            /* calculate the maximum allowed step size */
            max_length = HIGHER_ORDER_BOUND;
            for(i=0 ; i<n ; i++)
            {
                double length = fabs(droot[i]/(root[i]-ext1[i]));
                if(length > max_length)
                { max_length = length; }
                length = fabs(droot[i]/(root[i]-ext1[i+1]));
                if(length > max_length)
                { max_length = length; }
                length = fabs(dpole[i]/(pole[i]-ext2[i]));
                if(length > max_length)
                { max_length = length; }
                length = fabs(dpole[i]/(pole[i]-ext2[i+1]));
                if(length > max_length)
                { max_length = length; }
            }
            max_length = HIGHER_ORDER_BOUND/(STEP_REDUCTION*max_length);

            /* reduce step size until progress is made or stagnation is reached */
            max_error = 2.0;
            while(max_error > old_max_error)
            {
                max_length *= STEP_REDUCTION;

                for(i=0 ; i<n ; i++)
                {
                    root2[i] = root[i] + max_length*droot[i];
                    pole2[i] = pole[i] + max_length*dpole[i];
                }

                error1 = global_extremum(n, num1, weight, root2, pole2, end1, map, ext1, val1, inc1);
                error2 = global_extremum(n, num2, weight, pole2, root2, end2, map, ext2, val2, inc2);
                max_error = error1*error2;
            }
            if(max_error == old_max_error)
            { progress = 0; }
            else
            { progress = 1; }

            /* update solution */
            old_max_error = max_error;
            for(i=0 ; i<n ; i++)
            {
                root[i] = root2[i];
                pole[i] = pole2[i];
            }

            /* reduce weight if possible */
            min_error1 = error1;
            min_error2 = error2;
            for(i=0 ; i<n+1 ; i++)
            {
                if(inc1[i] == 0 && val1[i] < min_error1)
                { min_error1 = val1[i]; }
                if(inc2[i] == 0 && val2[i] < min_error2)
                { min_error2 = val2[i]; }
            }
            if(min_error1/error1 > EQUIOSCILLATION_DEVIATION && min_error2/error2 > EQUIOSCILLATION_DEVIATION)
            {
                if(min_error1/error1 > min_error2/error2)
                { weight *= EQUIOSCILLATION_DEVIATION*error2/min_error2; }
                else
                { weight *= EQUIOSCILLATION_DEVIATION*error1/min_error1; }
            }

            /* test for instability */
            instability = 0;
            for(i=0 ; i<n ; i++)
            {
                if(inc1[i] == 0 || inc2[i] == 0)
                { instability = 1; }
            }
        }

        /* deallocate memory */
        free(pole2);
        free(root2);
        free(dpole);
        free(droot);
    }

    /* calculate the Lebesgue-like constants */
    lebesgue[0] = global_lebesgue(n, num1, root, pole, end1, map, ext1, val1, inc1, work);
    lebesgue[1] = global_lebesgue(n, num2, pole, root, end2, map, ext2, val2, inc2, work);

    /* map solution on the standard domain back to the original domain */
    for(i=0 ; i<n ; i++)
    {
        root[i] = mobius(root[i], map);
        pole[i] = mobius(pole[i], map);
    }
    qsort(pole, n, sizeof(double), pole_cmp);

    /* deallocate memory */
    free(work);
    free(val2);
    free(val1);
    free(ext2);
    free(ext1);
    free(inc2);
    free(inc1);

    return max_error;
}

/* implementation of command-line interface */
int main(int argc, char **argv)
{
    int n, num1, num2, i;
    double *end1, *end2, *root, *pole, lebesgue[2], error;
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
    end1 = (double*)malloc(sizeof(double)*2*num1);
    for(i=0 ; i<num1 ; i++)
    {
        fscanf(input_file, "%lf %lf", end1+2*i, end1+2*i+1);
        if( (i && end1[2*i] < end1[2*i-1]) || end1[2*i+1] < end1[2*i])
        { printf("ERROR: endpoints in 1st domain are misordered\n"); return 0; }
    }
    fclose(input_file);

    input_file = fopen(argv[3], "r");
    fscanf(input_file, "%d", &num2);
    end2 = (double*)malloc(sizeof(double)*2*num2);
    for(i=0 ; i<num2 ; i++)
    {
        fscanf(input_file, "%lf %lf", end2+2*i, end2+2*i+1);
        if( (i && end2[2*i] < end2[2*i-1]) || end2[2*i+1] < end2[2*i])
        { printf("ERROR: endpoints in 2nd domain are misordered\n"); return 0; }

    }
    fclose(input_file);

    error = zolotarev_number(n, num1, num2, end1, end2, root, pole, lebesgue);
    printf("Z(%d) = %15.15e\n", n, error);
    printf("Lebesgue-like constant for 1st domain = %15.15e\n", lebesgue[0]);
    printf("Lebesgue-like constant for 2nd domain = %15.15e\n", lebesgue[1]);
    for(i=0 ; i<n ; i++)
    { printf("root[%d] = %15.15e\n", i, root[i]); }
    for(i=0 ; i<n ; i++)
    { printf("pole[%d] = %15.15e\n", i, pole[i]); }

    free(end2);
    free(end1);
    free(pole);
    free(root);

    return 1;
}
