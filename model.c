// Model based on lpaq1

enum {SMC=1,APM1,DS,AVG,SCM,RCM,CM,MX,ST,MM,DHS,SM,SK,APM2,ERR,TAPM,UAS,LMX,STA};
enum {S=8}; // S number of contexts
// N   last buffer index, n/2-1
// HN  last hash table index, n/8-1
enum {N=0xFFFFFFF,HN=0x3FFFFFF};
int ht[              0x4000000]={};
enum {MAXLEN=62};   // maximum match length, at most 62
int pos;      // number of bytes in buf
int match;    // pointer to current byte in matched context in buf
int len;      // length of match
int ha1, ha2; // context hashes
int order,c;
int cxt[8]={};
int t1[256]={};
char buf[0x10000000]={};
int apmfails,uaslimit,uasfails;
int ord[63]={};
//parameters
//mixer
int m_p[3]={8, 0, 28};
//err->apm, e_h also for uas
int e_l[8]={458, 985, 40, 554, 1548, 513, 1393, 954};
int e_h[8]={2536, 2734, 2190, 2221, 3081, 2129, 2576, 2745};

void mm_p(int y, int bpos,int c0) {
  int i,b,cx;

  if (bpos==0) {
    ha1=(ha1*(3<<3)+c)&HN;
    ha2=(ha2*(5<<5)+c)&HN;

    // find or extend match
    if (len>0) {
      ++match;
      match=match&N;
      if (len<MAXLEN) ++len;
    }
    else {
      match=ht[ha1];
      if (match!=pos) {
        while (len<MAXLEN && (i=(match-len-1)&N)!=pos && buf[i]==buf[(pos-len-1)&N])
          ++len;
      }
    }
    if (len<2) {
      len=0;
      match=ht[ha2];
      if (match!=pos) {
        while (len<MAXLEN && (i=(match-len-1)&N)!=pos && buf[i]==buf[(pos-len-1)&N])
          ++len;
      }
    }
    // update index
    ht[ha1]=pos;
    ht[ha2]=pos;
  }

  // predict
  cx=c0;
  if (len>0 && ((buf[match]+256)>>(8-bpos))==c0) {
    b=(buf[match]>>(7-bpos))&1;  // next bit
    if (len<16) cx=len*2+b;
    else cx=(len>>2)*2+b+24;
    cx=cx*256+buf[(pos-1)&N];
  }
  else
    len=0;

  vmx(SMC,0,cx);
}
int hash1(int i) {  i=i*123456791; i=i<<16|i>>16; return (i*987654323); }
int hash2(int i) {  i=i*123456791; i=i<<19|i>>13; return (i*987654323); }

// update is called in VM after every bit
int update(int y,int c0,int bpos,int c4,int pr){ 
    int i,a,j;
    order=0;
    apmfails=apmfails<<1;
    uasfails=uasfails<<1;
    j=y?pr^4095:pr;
    j=vmx(ERR,bpos,j);
    apmfails=apmfails|j;
    uasfails=uasfails|(j&1);
    if (bpos== 0){ 
        uaslimit=uasfails;
        buf[pos]=c4&0xff;
        pos++;
        pos=pos&N;

        c=c4&0xff;
        cxt[0]=c<<8;                                // order 1
        cxt[1]=(((c4&0xffff)<<5)|0x57000000);       // order 2
        cxt[2]=((c4<<8)*3);                         // order 3
        cxt[3]=(c4*5);                              // order 4
        cxt[4]=((cxt[4]*(11<<5)+c*13)&0x3fffffff);  // order 6
        if (c>=65 && c<=90) c=c+32;                 // lowercase unigram word order
        if (c>=97 && c<=122) cxt[5]=(cxt[5]+c)*(7<<3);
        else cxt[5]=0;
        cxt[6]=hash1(c4&0x00ff00ff);                // sparse
        i=(c4>>8)&0xff;
        t1[i]=(t1[i]<<8)|c;
        i=c|t1[c]<<8;
        cxt[7]=hash2(i&0xffff);                     // indirect
        for (i=1; i<S; i++) {
            if (cxt[i]==0) cxt[i]=256; //must be above 255
            a=vmx(DHS,0,cxt[i]);
            if (i<5) order=order+a;
        }
    }else {
        if (bpos==4){
            for ( i=1; i<S; i++) {
                j=cxt[i]+c0;
                a=vmx(DHS,0,j);
                if (i<5) order=order+a;
            }
        }else {
            j=(y+1)<<(bpos&3)-1;
            for ( i=1; i<S; i++) {
                a=vmx(DHS,0,j);
                if (i<5) order=order+a;
            }
        }
    }
    vmx(DS,0,cxt[0]+c0);
    mm_p(y,bpos, c0);// match
    if (len>0)order=ord[len];
    vmx(MX,0,order+10*(cxt[0]>>13));
    vmx(APM2,0,cxt[0]+c0); 
    vmx(APM2,1,apmfails*8+bpos);
    vmx(UAS,0,uaslimit);
    return 0;
}
//VM calls this after every block
void block(int a,int b) { 
    //get block info
}
// main is called only once after VM init.
int main() { 
    int i,e;
    for (i=1; i<63; ++i) ord[i]=5+(i>=8)+(i>=12)+(i>=16)+(i>=32);
    vms(1,0,1,0,0,0,0,1,0,2+S,1,0,0,2,8,0,1,2,0,0); 
    vmi(DS,0,17,1023 ,1);       // order 1
    vmi(DHS,0,4,26+(3<<8),S-1); // order 2+
    vmi(UAS,0,16,13,5);         // unaligned 16 bits, mask 13(ignored), rate 5
    for (i=0;i<S+1;i++) vmi(MM,i,0,i,0);
    vmi(SMC,0,64<<8,1023,0);   // match
    vmi(MX,0,m_p[0] +256*m_p[1]+0x1000000*m_p[2],80 ,0);
    for (i=0;i<8;i++) vmi(ERR,i,e_l[i]+(e_h[i]<<16),0,0);

    vmi(APM2,0,0x10000,24+6*256,S+1);
    vmi(LMX,0,S+1+(S+1+1)*256,2307,0);       // mx apm0
    vmi(APM2,1,0x800,24+40*256,S+1+1+1);
    vmi(LMX,1,S+1+1+(S+1+1+1+1)*256,2986,0); // apm0 apm1
}
