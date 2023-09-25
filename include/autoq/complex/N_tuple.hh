
#ifndef _AUTOQ_COMPLEX_HH_
#define _AUTOQ_COMPLEX_HH_


#include <iostream>
#include <vector>
#include <boost/rational.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include <cmath>
using namespace std;

namespace AUTOQ
{
	namespace Complex
	{
        class rational ;
        class N_tuple;
	}
}

int gcd(int a, int b)
{
  if (b == 0)
  {
    return a;
  }
  if (a == 0)
  {
    return 1;
  }

  return gcd(b, a % b);
}

class rational
{
private:
  

public:

  int numerator;
  int denominator;
  
  rational()
  {
    numerator = 0;
    denominator = 1;
  }
  rational(int n, int d)
  {
    if (n >= 0 && d >= 0)
    {
      numerator = n;
      denominator = d;
    }
    if (n <= 0 && d >= 0)
    {
      numerator = n;
      denominator = d;
    }
    if (d <= 0)
    {
      numerator = (-1) * n;
      denominator = (-1) * d;
    }
    
  }

  void show()
  {
    cout << this->numerator << "/" << this->denominator;
  }
  rational operator+(const rational &rational_b)
  {
    rational tmp;
    tmp.numerator = (rational_b.numerator * this->denominator) + (this->numerator * rational_b.denominator);
    tmp.denominator = rational_b.denominator * this->denominator;
    simplify(tmp);

    return tmp;
  }
  rational operator-(const rational &rational_b)
  {
    rational tmp;

    tmp.numerator = (this->numerator * rational_b.denominator) - (this->denominator * rational_b.numerator);
    tmp.denominator = rational_b.denominator * this->denominator;
    simplify(tmp);
    if (tmp.denominator <= 0)
    {
      tmp.numerator = (-1) * tmp.numerator;
      tmp.denominator = (-1) * tmp.denominator;
    }

    return tmp;
  }
  rational operator*(const rational &rational_b)
  {
    rational tmp;
    tmp.numerator = this->numerator * rational_b.numerator;
    tmp.denominator = this->denominator * rational_b.denominator;
    simplify(tmp);

    return tmp;
  }
  void simplify(rational &r)
  {
    int g;
    g = gcd(r.denominator, r.numerator);
    r.numerator = r.numerator / g;
    r.denominator = r.denominator / g;
    if (r.denominator <= 0)
    {
      r.numerator = r.numerator * (-1);
      r.denominator = r.denominator * (-1);
    }
  }
  void simplify(){
    int g; 
    g = gcd(this->denominator,this->numerator);
    this->numerator = this->numerator/g;
    this->denominator = this->denominator/g;
    if (this->denominator <= 0)
    {
      this->numerator = this->numerator * (-1);
      this->denominator = this->denominator * (-1);
    }
    
  }

  rational operator/(const rational &rational_b)
  {
    rational tmp;
    tmp.numerator = this->numerator * rational_b.denominator;
    tmp.denominator = this->denominator * rational_b.numerator;

    simplify(tmp);

    return tmp;
  }

  rational &operator=(const rational &rational_b)
  {

    this->numerator = rational_b.numerator;
    this->denominator = rational_b.denominator;
    return *this;
  }

  rational &operator+=(const rational &rational_b)
  {
    *this = *this + rational_b;

    return *this;
  }
  bool operator!=(const rational &rational_b){
    if (this->numerator == rational_b.numerator && this->denominator == rational_b.denominator  )
    {
      return 0;
    }
    else return 1;
  }

  bool operator<(const  rational   &rational_b){
     rational tmp_1;
     tmp_1 = *this - rational_b ; 
     if(tmp_1.numerator < 0) return 1; 
     else return 0 ;
      
     
  }
  
};

struct N_tuple
{
private:
const static long int  N = 4;  //the cyclomotic polynomial has highest degree of N
public:
  rational coeff[2*N];
  long int deg;
 
  template <typename T>
  N_tuple(T in)
  {
    deg = 0;
    for (long int i = 0; i < 2*N; i++)
    {
      coeff[i].numerator = 0;
      coeff[i].denominator = 1;
    }
  }
  template <typename T>
  N_tuple()
  {
    deg = 0;
    for (long int i = 0; i < 2*N; i++)
    {
      coeff[i].numerator = 0;
      coeff[i].denominator = 1;
    }
  }
  
  void set(rational a, long int d)
  { if(d > N) {cout << "invalid power";}
    else{
    coeff[d].numerator = a.numerator;
    coeff[d].denominator = a.denominator;
    coeff[d].simplify();
    deg = degree();
    }
  }
  void set_to_zeros()
  {
    for (long int i = 0; i <= deg; i++)
    {
      coeff[i].numerator = 0;
      coeff[i].denominator = 1;
    }
    deg = degree();
  }

  long int degree()
  {
    long int d = 0;
    for (long int i = 0; i < 2*N; i++)
    {
      if (coeff[i].numerator != 0)
      {
        d = i;
      }
    }
    deg = d;
    return d;
  }
  rational operator[](long int idx)
  {
    return coeff[idx];
  }
  void zero()
  {
    for (long int i = 0; i <= deg; i++)
    {
      coeff[i].numerator = 0;
      coeff[i].denominator = 1;
    }
    deg = degree();
  }
  void one()
  {
    rational one(1, 1);
    Zero();
    set(one, 0);
  }

  static N_tuple Zero()
  {
    return N_tuple(2);
  }
  static N_tuple One()
  {
    rational one(1, 1);
    N_tuple p = N_tuple(0);
    p.set(one, 0);
    return p;
  }
  static N_tuple sqrt2()    //TODO :for N_tuple now only when N=4
  {
    rational one(1, 1);
    rational minus_one(-1,1);

    N_tuple p = N_tuple(0);
    p.set(one, 1);
    p.set(minus_one , 3);

    

    return p;
  }
  static N_tuple Rand()
  {
   
   N_tuple p = N_tuple(0);
   for (size_t i = 0; i < N; i++)
   {rational tmp((rand() - 2147483646/2)%10000,(rand() +1)%100000);
     p.set(tmp,i);
    
   }

   
   return p;
  }
  static N_tuple Angle(rational &r){
      
    N_tuple p = N_tuple(0);
    if (N % r.denominator != 0 ) {
      cout << "invalid angle";
      return p;
      }
    else
    {
      rational one(1,1);
      p.set(one, N*r.numerator/r.denominator);
      return p;
    }
  
  }
  N_tuple fraction_simplification(){
    return *this;
  }
  std::string realToSMT() const {
    std::string result;
    double rl;
     rl = 0;
     
    for (long int  i = 0; i <= this->deg; i++)
    { double tmp = (double)this->coeff[i].numerator / this->coeff[i].denominator;
       
      rl += (double)tmp * cos(i*M_PI/N);
      
    }
    result = to_string(rl);
    return result;

    }
    std::string imagToSMT() const {
    std::string result;
    double im;
     
     im = 0; 
    for (long int  i = 0; i <= this->deg; i++)
    { double tmp = (double)this->coeff[i].numerator / this->coeff[i].denominator;
      
      im +=  (double)tmp * sin(i*M_PI/N);

    }
    
    result = to_string(im);
    return result;
    }
  
  double abs2(){
    double rl, im;
     rl = 0;
     im = 0; 
    for (long int  i = 0; i <= this->deg; i++)
    { double tmp = (double)this->coeff[i].numerator / this->coeff[i].denominator;
      cout << "n and d are " <<this->coeff[i].numerator <<" " <<  this->coeff[i].denominator <<endl;
      cout << "tmp is " << tmp << endl; 
      rl += (double)tmp * cos(i*M_PI/N);
      im +=  (double)tmp * sin(i*M_PI/N);

    }
    cout << "rl is" <<rl <<endl;
    cout << "im is " << im << endl;
    return (rl*rl + im *im);
     
  }


  N_tuple divide_by_the_square_root_of_two(int times=1){
    N_tuple sqrt = N_tuple(0).sqrt2();

    *this = *this  * sqrt;
    return *this;
  }
 
  rational to_rational(){
    if (this->deg ==0)
    { 
      return coeff[0];
      
    }
    else{cout << "this is not a rational " << endl;}
    return coeff[deg+1];
  }

  int to_int(){
    if (this->deg ==0 && this->coeff[0].denominator == 1){
      return this->coeff[0].numerator;
    }
    else{cout << "this is not a int" << endl;}
    return 0;
  }



  void show()
  {
    for (long int i = this->deg; i >= 0; i--)
    {
      this->coeff[i].show();
      cout << "x^" << i;
      if (i > 0)
      {
        cout << "+";
      }
    }
    cout << endl;
  }
  friend std::ostream& operator<<(std::ostream& os, const N_tuple& obj) {
      for (long int  i = obj.deg; i >= 0; i --)
      {
       os <<  obj.coeff[i].numerator <<  "/" << obj.coeff[i].denominator <<"x^" << i;
       if( i != 0 ) os << "+";
      }
      os << endl;
      
        
        return os;
    }
  N_tuple counterclockwise(rational &r){
      N_tuple tmp = N_tuple(0).Angle(r);
      *this = *this * tmp;
      return *this;
  }

  N_tuple clockwise(rational &r){
    rational minus_one(-1,1);
    rational one(1,1);
    *this = *this *minus_one;
    rational tmp = one - r;
    this->counterclockwise(tmp );
    return *this;
  }
  N_tuple operator=(const N_tuple &poly_b)
  {
    this->set_to_zeros();
    for (long int i = 0; i <= max(poly_b.deg, this->deg); i++)
    {
      this->coeff[i].numerator = poly_b.coeff[i].numerator;
      this->coeff[i].denominator = poly_b.coeff[i].denominator;
    }
    this->deg = poly_b.deg;
    return *this;
  }

  

  N_tuple operator+(const N_tuple &poly_b)
  {
    N_tuple tmp(0); // Cn we use emoty argument in constructor?
    for (int i = 0; i <= max(poly_b.deg, this->deg); i++)
    {
      tmp.coeff[i] = this->coeff[i] + poly_b.coeff[i];
    }
    tmp.degree();
    return tmp;
  }

  N_tuple operator-(const N_tuple &poly_b)
  {
    N_tuple tmp(0); // Cn we use emoty argument in constructor?
    for (int i = 0; i <= max(poly_b.deg, this->deg); i++)
    {
      this->coeff[i] = this->coeff[i] - poly_b.coeff[i];
    }

    tmp.degree();
    return tmp;
  }
  N_tuple operator*(const rational &r)
  {
    N_tuple tmp(0);
    for (int i = 0; i <= this->deg; i++)
    {
      tmp.coeff[i] = this->coeff[i] * r;
    }
    tmp.degree();
    return tmp;
  }
  N_tuple operator%(N_tuple &poly_b)
  {

    N_tuple tmp(0);
    tmp = *this;
    while (tmp.deg >= poly_b.deg)
    {
      rational r;

      r = tmp.coeff[tmp.deg] / poly_b[poly_b.deg];
      for (long int i = poly_b.deg; i >= 0; i--)
      {
        rational t;
        tmp.coeff[tmp.deg - i] = tmp.coeff[tmp.deg - i] - (r * poly_b[poly_b.deg - i]);
        t = this->coeff[tmp.deg - i] - (r * poly_b[poly_b.deg - i]);
      }

      tmp.degree();
    }
    return tmp;
  }
  N_tuple operator*(N_tuple &poly_b)
  {
    N_tuple tmp(0);
    for (long int i = 0; i <= this->deg + poly_b.deg; i++)
    {
      for (long int j = 0; j <= i; j++)
      {
        tmp.coeff[i] += this->coeff[j] * poly_b[i - j];
      }
    }
    tmp.degree();
    // cout<<tmp.deg <<endl;
    // tmp.show();
    N_tuple cyclo_poly(0);
    rational one(1, 1);
    cyclo_poly.set(one, 4);
    cyclo_poly.set(one, 0);
    tmp = tmp % cyclo_poly;
    // cout<<tmp.deg <<endl;
    // cyclo_poly.show();
    // tmp.show();

    return tmp;
  }
  N_tuple operator/ (rational &r){
    for (long int  i = 0 ; i <= this->deg ; i++)
    {
      this->coeff[i] = this->coeff[i] / r;
      coeff[i].simplify();
    }
    this->degree();
    return *this;
  }
  bool operator==(const N_tuple &poly_b){
    if (this->deg == poly_b.deg)
    { for (long int  i = 0; i <= this->deg; i++)
    { 
      if (this->coeff[i] != poly_b.coeff[i])
    { 
      return 0; 
    }
   
    }
         
    } 
    return 1;
  }
  bool operator<(const N_tuple poly_b){
    if (this->deg < poly_b.deg) return 1;
    else if (this->deg >poly_b.deg) return 0;
    else{
      for (long int  i = this->deg; i >= 0; i--)
      { if (this->coeff[i] != poly_b.coeff[i])
      {  if(this->coeff[i] <poly_b.coeff[i]) return 1;
        
      }
      
        
      }
      return 0;
    }
    
    
    
  }
  bool isZero(){
     if (this->deg == 0 && this->coeff[0].numerator == 0)
     {
      return 1;
     }
     else return 0;
  }
};

#endif
