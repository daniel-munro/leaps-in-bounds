// Second independently written exact global verifier for 10-line arrangements.
// Uses insertion-sorted intersection rational abscissas and Lehmer-coded
// cyclic-end-normalized line crossing orders, with a different layout/hash
// implementation from the generator. Full packed keys compared on collisions.
#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <cstdint>
#include <algorithm>
using namespace std;
using i64=int64_t;
struct L {i64 slope,offset;};
struct Rat {i64 a,b;unsigned char line;};
struct Signature {uint64_t u[3];};
struct HSet {
 vector<Signature> buckets;uint64_t mask,occupied;
 HSet(int n):buckets(1ull<<n),mask((1ull<<n)-1),occupied(0){}
 static uint64_t rotate(uint64_t w,int b){return (w<<b)|(w>>(64-b));}
 static uint64_t murmur(uint64_t v){v^=v>>33;v*=0xff51afd7ed558ccdULL;v^=v>>33;v*=0xc4ceb9fe1a85ec53ULL;return v^(v>>33);}
 bool add(const Signature& s){
   uint64_t h=murmur(s.u[0]+rotate(s.u[1],17)+rotate(s.u[2],41));
   for(size_t i=h&mask;;i=(i+1)&mask){
      auto& t=buckets[i];
      if((t.u[0]|t.u[1]|t.u[2])==0){t=s;occupied++;return true;}
      if(t.u[0]==s.u[0]&&t.u[1]==s.u[1]&&t.u[2]==s.u[2])return false;
   }
 }
};
inline bool less_rat(const Rat& x,const Rat& y){return (__int128)x.a*y.b < (__int128)y.a*x.b;}
inline bool sig(const array<L,10>& lines,Signature& out){
  unsigned char visits[10][9];
  for(int i=0;i<10;i++){
    Rat ordered[9];int n=0;
    for(int j=0;j<10;j++)if(j!=i){
      i64 den=lines[j].slope-lines[i].slope,num=lines[i].offset-lines[j].offset;
      if(den==0)return false;
      if(den<0){den=-den;num=-num;}
      Rat v{num,den,(unsigned char)j};
      int k=n++;
      while(k && less_rat(v,ordered[k-1])){ordered[k]=ordered[k-1];--k;}
      ordered[k]=v;
    }
    for(int j=1;j<9;j++)if(!less_rat(ordered[j-1],ordered[j]))return false;
    for(int j=0;j<9;j++)visits[i][j]=ordered[j].line;
  }
  // Independently enumerate all 20 cyclic starting ends and their reversals.
  unsigned char canonical[90],sample[90];
  for(auto &x:canonical)x=255;
  for(int reverse=0;reverse<2;reverse++)for(int offset=0;offset<20;offset++){
    int seen[10],serial[10],first_end[10],new_index[10];
    fill(seen,seen+10,0);int count=0;
    for(int e=0;e<20;e++){
      int position=(offset + (reverse ? 20-e : e))%20;
      int v=position%10;
      if(!seen[v]){seen[v]=1;serial[count++]=v;first_end[v]=position;}
    }
    if(count!=10)return false;
    for(int k=0;k<10;k++)new_index[serial[k]]=k;
    int at=0;bool smaller=false,reject=false;
    for(int q=0;q<10 && !reject;q++){
      int v=serial[q];bool walk_from_positive=first_end[v]<10;
      for(int r=0;r<9;r++){
        int line=visits[v][walk_from_positive ? (8-r) : r];
        auto digit=(unsigned char)new_index[line];
        if(!smaller){
          if(digit>canonical[at]){reject=true;break;}
          if(digit<canonical[at])smaller=true;
        }
        sample[at++]=digit;
      }
    }
    if(!reject && smaller)copy(sample,sample+90,canonical);
  }
  // Rank each 9-permutation by factorial number system (Lehmer code): 19 bits.
  const uint32_t factorial[9]={1,1,2,6,24,120,720,5040,40320};
  out.u[0]=out.u[1]=out.u[2]=0;
  for(int line=0;line<10;line++){
    uint32_t bitmap=0,rank=0;
    for(int index=0;index<9;index++){
      uint32_t symbol=canonical[line*9+index];
      if(symbol>=10 || symbol==(uint32_t)line)return false;
      if(symbol>(uint32_t)line)symbol--;
      if(bitmap&(1u<<symbol))return false;
      uint32_t lesser=0;
      for(uint32_t y=0;y<symbol;y++)lesser+=!(bitmap&(1u<<y));
      rank+=lesser*factorial[8-index];
      bitmap|=1u<<symbol;
    }
    if(bitmap!=511||rank>=362880)return false;
    int begin=19*line,w=begin/64,k=begin%64;
    out.u[w]|=uint64_t(rank)<<k;
    if(k+19>64)out.u[w+1]|=uint64_t(rank)>>(64-k);
  }
  out.u[2]|=(1ull<<63);return true;
}

int main(int argc,char**argv){
 if(argc!=12){cerr<<"usage: verify_113m BASE_ROWS OLD_COUNT OLD_BIN NEW_COUNT NEW_BIN CHAMBER_COUNT CHAMBER_BIN EXTRA_COUNT EXTRA_BIN NEW_COUNT NEW_BIN\n";return 2;}
 uint64_t base=stoull(argv[1]),oldCount=stoull(argv[2]),newCount=stoull(argv[4]);
 ios::sync_with_stdio(false);cin.tie(nullptr);
 HSet set(27);
 array<L,10>lines;
 for(uint64_t b=0;b<base;b++){
    for(int k=0;k<10;k++){
       i64 a,b_,c;if(!(cin>>a>>b_>>c)){cerr<<"missing original row "<<b<<"\n";return 3;}
       if(a!=-k||b_!=1){cerr<<"bad original row "<<b<<","<<k<<"\n";return 4;}
       lines[k]={-a,c};
    }
    Signature s;if(!sig(lines,s)||!set.add(s)){cerr<<"BASE_GEOMETRY_OR_DUPLICATE "<<b<<"\n";return 5;}
    if((b+1)%2000000==0)cerr<<"SECOND_ORIGINAL "<<b+1<<"\n";
 }
 auto checkCompact=[&](const char *path,uint64_t number,int gapUpper,int32_t tUpper,int code){
   ifstream input(path,ios::binary);if(!input){cerr<<"MISSING "<<path<<"\n";return code;}
   for(uint64_t b=0;b<number;b++){
     uint8_t gaps[9];int32_t t[9];
     input.read((char*)gaps,9);input.read((char*)t,36);
     if(!input){cerr<<"SHORT "<<path<<" "<<b<<"\n";return code;}
     lines[0]={0,0};
     for(int k=1;k<10;k++){
       if(gaps[k-1]<1||gaps[k-1]>gapUpper||t[k-1]<-tUpper||t[k-1]>tUpper){cerr<<"BAD_RANGE "<<b<<"\n";return code;}
       lines[k]={lines[k-1].slope+gaps[k-1],t[k-1]};
     }
     Signature s;if(!sig(lines,s)||!set.add(s)){cerr<<"COMPACT_GEOMETRY_OR_DUPLICATE "<<path<<" "<<b<<"\n";return code;}
     if((b+1)%2000000==0)cerr<<"SECOND_COMPACT "<<path<<" "<<b+1<<" TOTAL="<<set.occupied<<"\n";
   }
   if(input.peek()!=EOF){cerr<<"TRAILING_BYTES "<<path<<"\n";return code;}
   return 0;
 };
 if(int rc=checkCompact(argv[3],oldCount,7,2000000,6))return rc;
 if(int rc=checkCompact(argv[5],newCount,31,30000000,7))return rc;
 if(int rc=checkCompact(argv[7],stoull(argv[6]),31,1000000000,9))return rc;
 if(int rc=checkCompact(argv[9],stoull(argv[8]),31,1000000000,11))return rc;
 if(int rc=checkCompact(argv[11],stoull(argv[10]),31,1000000000,12))return rc;
 if(set.occupied!=base+oldCount+newCount+stoull(argv[6])+stoull(argv[8])+stoull(argv[10])){cerr<<"WRONG_COUNT "<<set.occupied<<"\n";return 8;}
 cout<<"PASS: independently canonicalized "<<set.occupied<<" inequivalent ten-line arrangements including reflections\n";
}
