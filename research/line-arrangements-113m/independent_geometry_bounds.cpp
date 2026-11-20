// Independently implemented exact geometric verification of compact binary witnesses.
// Uses oriented determinants over all unordered triples, not the generator's
// pairwise crossing-order sorter. No floating point anywhere.
#include <array>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <fstream>
using namespace std;
int main(int argc,char**argv){
 if(argc!=5){cerr<<"usage: independent_compact_geometry DATA EXPECTED_ROWS GAP_MAX ABS_INTERCEPT_MAX\n";return 2;}
 ifstream f(argv[1],ios::binary);if(!f){cerr<<"not found\n";return 2;}
 uint64_t expected=stoull(argv[2]),count=0;
 int gapMax=stoi(argv[3]),interceptMax=stoi(argv[4]);
 unsigned char d[9];int32_t y[10];int64_t m[10];
 y[0]=0;m[0]=0;
 for(;;){
   f.read((char*)d,9);
   if(f.gcount()==0)break;
   if(f.gcount()!=9){cerr<<"truncated gap bytes at "<<count<<"\n";return 4;}
   f.read((char*)&y[1],9*4);
   if(f.gcount()!=9*4){cerr<<"truncated intercept bytes at "<<count<<"\n";return 5;}
   for(int i=1;i<10;i++){
     if(d[i-1]<1 || d[i-1]>gapMax || y[i]<-interceptMax || y[i]>interceptMax){cerr<<"invalid coordinates row "<<count<<"\n";return 6;}
     m[i]=m[i-1]+d[i-1];
   }
   for(int i=0;i<10;i++)for(int j=i+1;j<10;j++)for(int k=j+1;k<10;k++){
       int64_t v=(m[i]-m[k])*((int64_t)y[i]-y[j])+(m[j]-m[i])*((int64_t)y[i]-y[k]);
       if(v==0){cerr<<"TRIPLE CONCURRENCE row "<<count<<" lines "<<i<<","<<j<<","<<k<<"\n";return 7;}
   }
   ++count;
   if(count%5000000==0)cerr<<"GEOMETRY_PASS "<<count<<"\n";
 }
 if(count!=expected){cerr<<"ROW COUNT MISMATCH "<<count<<" expected "<<expected<<"\n";return 9;}
 cout<<"PASS: "<<count<<" new variable-slope arrangements; all 45 pairs intersect and all 120 line triples are nonconcurrent for every arrangement\n";
}
