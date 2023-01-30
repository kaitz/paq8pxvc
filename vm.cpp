// c4.c - C in four functions

// char, int, and pointer types
// if, while, return, for and expression statements

// Written by Robert Swierczek
// + x86 JIT compiler by Dmytro Sirenko
// + win32 port by Joe Bogner
// + port to paq Kaido Orav


enum { VMCOMPRESS=0,VMDETECT,VMENCODE,VMDECODE};
#ifdef VMMSG
#define kprintf printf // prints error messages
//#define dprintf printf // prints x86 asm to console
#define dprintf(...)  // prints x86 asm to console
#else
#define kprintf(...)    
#define dprintf(...)    
#endif
//vmi - init components
enum {vmSMC=1,vmAPM1,vmDS,vmAVG,vmSCM,vmRCM,vmCM,vmMX,vmST,vmMM,vmDHS,vmSM,vmSK,vmAPM2,vmERR,vmTAPM,vmUAS,vmLMX,vmSTA,vmBYT};
const char* cNames[]={
"SMC","APM","DS ","AVG","SCM","RCM","CM ","MX ","ST ","MM ","DHS","SM ","SK ","AP2","ERR","TAP","UAS","LMX","STA","BYT"
};

class VM {

public:
    
    BlockData& x;
    Array<int> prSize; // size in bytes of memory in mem[mindex]   
    int totalPR;
    Array<int> mcomp;  //component list set in vmi
    Array<ContextMap *>cmC;
    int smc, apm1, rcm, scm, cm, mx,st,av,ds,mm,dhs,sm,sk,apm2,em,tapm,uas,lmx,statec,byt;

    MixMap1 mmA[256];
    Mixer1 mxA[256];
    StaticMap stA[256];
    DynamicSMap dsA[256];
    DynamicHSMap dhsA[256];
    APM1 apm1A[256];
    StateMapContext smA[256];
    AvgMap  avA[256];   
    SmallStationaryContextMap scmA[256];    
    StationaryMap smcA[256];    
    RunContextMap rcmA[256];  
    SkMap skA[256];  
    APM2 apm2A[256];
    ErrMap emA[256];
    TAPM tapmA[256];
    UAS uasA[256];
    LmxMap  lmxA[256];   
    ByteMap bmA[256];
    int totalc;  //total number of components
    int currentc; //current component, used in vmi
    int initdone; //set to 1 after main exits
    int mindex;        // count fo memory allocations
    FILE *inFile, *outFile; // files for decoding and encoding
    int inpos;
    int plpos;
    StateTable  vmstate;
    U8 vm_nn[256][512*4]={  };
    U8 nn01[256][256];
VM(BlockData& bd);
~VM() ;
void next();
void expr(int lev);
void stmt();
int dovm(int *ttt);
void gen(int *n);
int  dojit();
int detect(int c4,int pos);
int decode(int info,int len);
int encode(int info,int len);
int block(int info1,int info2);
int doupdate1(int y, int c0, int bpos,U32 c4,int pos);
int doupdate2(int y, int c0, int bpos,U32 c4,int pos);

void killvm( );
void decompile();
int getPrediction( );
void updateComponents(int p);
void init(){
     totalc=currentc; //update total count to current count 
      prSize.resize(totalPR--);
   
    // if mixer is used parse all input arrays
    if(x.cInputs>=0 && x.cInputs<256){ 
        // init input arrays
        for (int j=0;j<x.cInputs+1;j++)  {
            x.mxInputs[j].ncount=(x.mxInputs[j].ncount+15)&-16;
            x.mxInputs[j].n.resize(x.mxInputs[j].ncount );
            // resize inputs[x] to correct size
        }     
        // provide inputs array info to mixers
        
        for (int i=0;i<totalc;i++){
            int prindex=mcomp[i]>>24;
            int compnr=(mcomp[i]>>8)&0xff;
            // individual components
            if (prindex>0 && compnr==vmMX){
                int index=(mcomp[i]>>16)&0xff;
                int input=mcomp[i]&0xff;
                // set input 
                mxA[index].setTxWx(x.mxInputs[input].n.size(),&x.mxInputs[input].n[0]);
                //maxMX=index;
            }
        }
    }
}
};
// alloc function in interpreted code
// keep track of pointers and sizes in bytes
// no bounds test

void VM::killvm( ){
    if ( smc>0 )  {
       for (int i=0;i<smc;i++)  smA[i].Free(); 
    }
    if ( apm1>0 ) {
        for (int i=0;i<apm1;i++) apm1A[i].Free();
    }
    if ( apm2>0 ) {
        for (int i=0;i<apm2;i++) apm2A[i].Free();
    }
        if ( tapm>0 ) {
        for (int i=0;i<tapm;i++) tapmA[i].Free();
    }
    if ( scm>0 ) {
        for (int i=0;i<scm;i++)  scmA[i].Free();
    }
    if ( cm>0 ) {
        for (int i=0;i<cm;i++) delete cmC[i]; 
    }
   if ( mx>0 ) {
        for (int i=0;i<mx;i++) mxA[i].Free();
    }
    if ( ds>0 ) {
        for (int i=0;i<ds;i++)  dsA[i].Free();
    }
    if ( dhs>0 ) {
        for (int i=0;i<dhs;i++)  dhsA[i].Free();
    }
    if ( sm>0 ) {
        for (int i=0;i<sm;i++)  smcA[i].Free();
    }
    if ( rcm>0 ) {
        for (int i=0;i<rcm;i++)  rcmA[i].Free();
    }
    if ( uas>0 ) {
        for (int i=0;i<uas;i++)  uasA[i].Free();
    }


    smc=apm1=apm2=tapm=rcm=scm=cm=mx=mm=st=av=ds=dhs=sm=sk=currentc=totalc=initdone=mindex=0;
    
  
}
//vms - set number of components
void components(VM* v,int a,int b,int c,int d,int e,int f,int g,int h,int i,int j,int k,int l,int m,int o,int p,int q,int r,int s,int sg,int bt){
    //if (v->initdone==1) {kprintf("VM vms error: vms allowed only in main\n ");quit();}
    if (v->totalc>0) {kprintf("VM vms error: vms allready called\n ");quit();}
    v->smc=a, v->apm1=b,v->ds=c,v->av=d,v->scm=e, v->rcm=f,   v->cm=g, v->mx=h,v->st=i,v->mm=j,v->dhs=k,v->sm=l,v->sk=m,v->apm2=o,v->em=p,v->tapm=q,v->uas=r,v->lmx=s,v->statec=sg,v->byt=bt;
    v->totalc= a+b+c+d+e+f+g+h+i+j+k+h+l+m+o+p+q+r+s+sg+bt;
    v->mcomp.resize(v->totalc); 
    if (v->totalc==0 && h>0) quit("No inputs for mixer defined VM\n");
}

void printcomponent(int component){
    printf("%s",cNames[component-1]);
}
//incremental mixer parameters - test

void initcomponent(VM* v,int component,int componentIndex, int f,int d, int indexOfInputs){
   // assert(componentIndex>=0); //component index
   // assert(d>=0); //component context
   int cms3=0,cms4=0,rd=0;
    if (component==vmCM) cms3=(indexOfInputs>>8)&255,cms4=(indexOfInputs>>16)&255,rd=(indexOfInputs>>28)&1,indexOfInputs=indexOfInputs&255;
    //printcomponent(component); printf(" component %d,  componentIndex %d,   f %d,  d %d,   indexOfInputs %d\n",component, componentIndex,  f, d,  indexOfInputs);
    //if (v->initdone==1) {kprintf("VM vmi error: vmi allowed only in main\n ");quit();}
    if (v->currentc>  v->totalc) {kprintf("VM vmi error: component %d not set %d - %d\n ",component,v->currentc, v->totalc);quit();}
    if (componentIndex>  255)  {kprintf("VM vmi error: componentIndex\n ");quit();}
    const int ii=componentIndex+1;
    bool isInputs= (component==vmAPM1 || component==vmAPM2 || component==vmTAPM || component==vmUAS||component==vmDS||component==vmERR||component==vmBYT||component==vmSTA|| component==vmDHS || component==vmAVG || (component==vmST && indexOfInputs==-1)||(component==vmSK && indexOfInputs==-1)||(component==vmSMC && indexOfInputs==-1));
    if (indexOfInputs>=0 &&  v->x.cInputs <indexOfInputs && isInputs==false){// input sets for mixers
        v->x.cInputs++;
        v->x.mxInputs.resize(v->x.mxInputs.size()+1);
        if(v->x.mxInputs.size()<=indexOfInputs){
        v->x.mxInputs.resize(indexOfInputs+1);
        v->x.cInputs=indexOfInputs;
        }
    }
   
    switch (component) {
    case vmSMC: {if ( indexOfInputs==-1)v->totalPR++; if (ii>v->smc ) {kprintf("VM vmi error: smc(%d) defined %d, max %d\n",component,ii, v->smc);quit(); } 
                if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount++;
        break; }
    case vmAPM1:{v->totalPR++; if (ii>v->apm1) {kprintf("VM vmi error: apm1(%d) defined %d, max %d\n",component,ii, v->apm1);quit();} 
        break; }
    case vmAPM2:{v->totalPR++; if (ii>v->apm2) {kprintf("VM vmi error: apm2(%d) defined %d, max %d\n",component,ii, v->apm2);quit();} 
        break; }
    case vmTAPM:{v->totalPR++; if (ii>v->tapm) {kprintf("VM vmi error: tapm(%d) defined %d, max %d\n",component,ii, v->tapm);quit();} 
        break; }   
    case vmUAS:{v->totalPR++; if (ii>v->uas) {kprintf("VM vmi error: uas(%d) defined %d, max %d\n",component,ii, v->uas);quit();} 
        break; }   
    case vmDS:{v->totalc=v->totalc+indexOfInputs-1;v->mcomp.resize(v->mcomp.size()+indexOfInputs); v->totalPR+=indexOfInputs; if (ii>v->ds) {kprintf("VM vmi error: ds(%d) defined %d, max %d\n",component,ii, v->ds);quit();}
          if (f<1) {kprintf("VM vmi error:ds(%d) memory bits must be larger then 0.",ii);quit();}
        break;      }
    case vmDHS:{v->totalc=v->totalc+indexOfInputs-1;v->mcomp.resize(v->mcomp.size()+indexOfInputs); v->totalPR+=indexOfInputs; if (ii>v->dhs) {kprintf("VM vmi error: dhs(%d) defined %d, max %d\n",component,ii, v->dhs);quit();}
          if (f<1) {kprintf("VM vmi error:dhs(%d) memory bits must be larger then 0.",ii);quit();}
        break;      }
    case vmRCM: { if (ii>v->rcm ) {kprintf("VM vmi error: rcm(%d) defined %d, max %d\n",component,ii, v->rcm);quit(); }
     if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount++;
        break;  }
    case vmSCM: { if (ii>v->scm ) {kprintf("VM vmi error: scm(%d) defined %d, max %d\n",component,ii, v->scm);quit(); }
     if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount+=2;
        break;  }
    case vmAVG:{ v->totalPR++; if (ii>v->av ) {kprintf("VM vmi error: AVG(%d) defined %d, max %d\n",component,ii, v->av);quit();}
        break;  }
    case vmLMX:{ v->totalPR++; if (ii>v->lmx ) {kprintf("VM vmi error: LMX(%d) defined %d, max %d\n",component,ii, v->lmx);quit();}
        break;  }
    case vmCM: {
        v->cmC.resize(v->cmC.size()+1);
        //if ( (indexOfInputs)>=0) v->x.mxInputs[(indexOfInputs)].ncount+=6*(d&255);
        break;  }
    case vmMX: {v->totalPR++;
        break;  }
    case vmST: {if ( indexOfInputs==-1)v->totalPR++; if (ii>v->st )  {kprintf("VM vmi error: st(%d) defined %d, max %d\n",component,ii, v->st);quit();}
        if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount++;
        break;  }
    case vmMM: { v->x.mxInputs[indexOfInputs].ncount++;
        break;  }
    case vmSM: { if (ii>v->sm ) {kprintf("VM vmi error: sm(%d) defined %d, max %d\n",component,ii, v->sm);quit(); }
     if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount+=2;
        break;  }
    case vmSK: { if ( indexOfInputs==-1)v->totalPR++;if (ii>v->sk ) {kprintf("VM vmi error: sk(%d) defined %d, max %d\n",component,ii, v->sk);quit(); }
     if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount+=1;
        break;  }
     case vmERR: {//if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount++;
        break;  } 
         case vmSTA: {//if ( indexOfInputs>=0) v->x.mxInputs[indexOfInputs].ncount++;
        break;  }     
      case vmBYT: {  break;  }    
    default: quit("VM vmi error\n");
    }

    int prindex=0;
    if (component==vmAPM1 || component==vmAPM2|| component==vmTAPM || component==vmUAS || component==vmDS|| component==vmDHS || component==vmAVG || component==vmLMX|| (component==vmST && indexOfInputs==-1)||(component==vmSK && indexOfInputs==-1)||(component==vmSMC && indexOfInputs==-1) || component==vmMX)prindex=v->totalPR;
    // If Autotune then ignore model parameters, first run is allways with model parameters.
    switch (component) {
    case vmSMC:{
        int smc_l=d;          // limit
        U8 *n=&v->vm_nn[0][0];
        v->smA[componentIndex].Init(f, smc_l,n);
        break;  
    } 
    case vmAPM1: {   
        int apm_l=d;          // limit
        v->apm1A[componentIndex].Init(f,apm_l,indexOfInputs);
        break;
    }
    case vmAPM2: {   
        int apm_l=d>>8;          // limit
        int apm_s=d&255;
        if (apm_l==0) apm_l=0;  
        if (apm_s==0) apm_s=24;      
        v->apm2A[componentIndex].Init(f,(apm_l<<8)+apm_s,indexOfInputs);
        break;
    }
    case vmTAPM: {   
        int apm_l0=f&0xffff;          // limit
        int apm_l1=f>>16;
        int apm_l2=d&0xfff;
        int apm_l3=(d>>12)&0xfff;
        int apm_l4=indexOfInputs&0xffff;
        int apm_w1=(indexOfInputs>>16)&0xff;//8
        int apm_w2=(indexOfInputs>>24)&0xff;//21
        int apm_wb1=(U32(d)>>24);
        // If Autotune then ignore model parameters, first run is allways with model parameters.
        
        v->tapmA[componentIndex].Init(apm_l0,apm_l1,apm_l2,apm_l3,apm_l4,apm_w1,apm_w2,apm_wb1);
        break;
    }
    case vmSTA: {   
        int sta_l0=f&0xffff;          // limit
        int sta_l1=f>>16;
        int sta_l2=d&0xffff;
        int sta_l3=(d>>16);
        int sta_l4=indexOfInputs&0xffff; 
        int sta_l5=(indexOfInputs>>16)&255;
        int sta_l6=(indexOfInputs>>24)&255;
        int isSta=sta_l0|sta_l1|sta_l2|sta_l3|sta_l4|sta_l5|sta_l6;
        if (isSta==0)sta_l0=42,sta_l1=41,sta_l2=13,sta_l3=6,sta_l4=5,sta_l5=16,sta_l6=14;
        v->vmstate.Init(sta_l0,sta_l1,sta_l2,sta_l3,sta_l4,sta_l5,sta_l6);
        for (int i=0;i<256;i++) v->vm_nn[componentIndex+1][i]=v->vmstate.next(i,0);
        for (int i=256;i<512;i++) v->vm_nn[componentIndex+1][i]=v->vmstate.next(i-256,1);
        for (int i=512;i<512+256;i++) v->vm_nn[componentIndex+1][i]=v->vmstate.next(i-512,2);
        for (int i=512+256;i<512+512;i++) v->vm_nn[componentIndex+1][i]=v->vmstate.next(i-256-512,3);
        for (int i=0;i<256;i++) {
            int n0=-!v->vmstate.next(i,2);
            int n1=-!v->vmstate.next(i,3);
            int r=0;
            if ((n1-n0)==1 ) r=2;
            if ((n1-n0)==-1 ) r=1;
            v->nn01[componentIndex+1][i]=r;
        }
        break;
    }
    case vmUAS: {   
        int bits=f;
        int mask=d;
        bool domask=false;
        int rate=indexOfInputs;
        if (rate==0) rate=5;
        //vm_uas_mask_max[componentIndex]=(1<<bits)-1;//set max mask
        v->uasA[componentIndex].Init(bits,mask,domask,rate);
        break;
    }
    case vmDS: {
        int ds_l=d;
        int stable=f>>16;
        
        U8 *n=&v->vm_nn[stable][0];
        v->dsA[componentIndex].Init(f&255,ds_l,indexOfInputs,n);
        break; }
    case vmDHS: {
        int stable=f>>16;
        U8 *n=&v->vm_nn[stable][0];
        v->dhsA[componentIndex].Init(f&255,d,indexOfInputs,n);
        break; }
    case vmRCM: {    
        int rcm_ml=d&255;          // limit
        if (rcm_ml==0) rcm_ml=8;
        // If Autotune then ignore model parameters, first run is allways with model parameters.
        
        v->rcmA[componentIndex].Init(f<=0?4096:f*4096,rcm_ml);
        break;}
    case vmSCM: v->scmA[componentIndex].Init(f); 
        break;
    case vmAVG:{
        int avg_l0=f&255;          // limit
        int avg_l1=(f>>8)&255;  
        if (avg_l0==0) avg_l0=1;
        if (avg_l1==0) avg_l1=1;
        v->avA[componentIndex].Init(indexOfInputs&0xff,(indexOfInputs>>8)&255,f,d);
        break;
    }
    case vmLMX:{
        int lmx_l0=f&255;          // limit
        int lmx_l1=(f>>8)&255;  
        int w=d;
        if (w==0) w=2048;
        
        v->lmxA[componentIndex].Init(lmx_l0,lmx_l1,w);
        break;
    }
    case vmERR:{
        int e_h=(U32(f)>>16);
        if (e_h==0) e_h=4095;
        int e_l=U32(f)&0xffff;
        if (e_l==0) e_l=2047;
        
        v->emA[componentIndex].Init(e_l,e_h);
        break;
    }    
    case vmBYT:{
        int b_v=U32(f)&0xff;
        //int b_l=U32(d)&0xff;
        v->bmA[componentIndex].Init(b_v);
        break;
    }       
    case vmCM:{
        int cm_l=(d>>8)&255;          // limit
        if (cm_l==0) cm_l=4;
        int cms_l=(d>>16)&255;          // sm rate
        if (cms_l==0) cms_l=32;
        int cms2_l=(U32(d)>>24)&255;          // sm2 rate
        if (cms2_l==0) cms2_l=12;
        if (cms3==0) cms3=32;
        if (cms4==0) cms4=12;
        int mem=f&0xffffff;
        int stindex=U32(f)>>24;
        // If Autotune then ignore model parameters, first run is allways with model parameters.
        
        U8 *n=&v->vm_nn[stindex][0];U8 *n1=&v->nn01[stindex][0];
        v->cmC[componentIndex] = (ContextMap*)new ContextMap(mem<=0?4096:mem*4096,(d&255)|(cm_l<<8)|(cms_l<<16)|(cms2_l<<24),v->x,cms3,n,n1,cms4,rd);
        if ( (indexOfInputs)>=0) v->x.mxInputs[(indexOfInputs)].ncount+=v->cmC[componentIndex]->inputs *(d&255);
        break;}
    case vmMX: {
        // read model info
        int mx_err=(f>>8)&0xffff; // err
        int mx_sh=f&255;          // shift
        if (mx_sh==0)mx_sh=64;
        int mx_ue=f>>24;
        if (mx_ue==0)mx_ue=28;
        v->mxA[componentIndex].Init(d,mx_sh,mx_err,mx_ue); //context,shift,err
        break;
    }
    case vmST: v->stA[componentIndex].Init(f,indexOfInputs);
        break;
    case vmMM: v->mmA[componentIndex].Init(d,f);
        break;
    case vmSM:{ 
        int sm_l=(d>>8)&255;          // limit
        int sm_b=d&255;  
        if (sm_l==0)sm_l=8<<1;
        v->smcA[componentIndex].Init(f,sm_b,sm_l); 
        break;}
    case vmSK:{ 
        v->skA[componentIndex].Init(); 
        break;}
    default:
        quit("VM vmi error\n");
        break;
    }
    int m=indexOfInputs;
    if (component==vmAVG || component==vmLMX ||component==vmAPM1|| component==vmAPM2|| component==vmTAPM|| component==vmERR|| component==vmBYT|| component==vmSTA|| component==vmUAS) m=0;
    if (indexOfInputs==-1) m=0;
     if (component==vmDS || component==vmDHS  ) {m=0;
     for (int j=0;j< indexOfInputs;j++) v->mcomp[v->currentc++] =m+((prindex-indexOfInputs+j+1)<<24)+(componentIndex<<16)+(component<<8);
     }else{
     
    v->mcomp[v->currentc++] =m+(prindex<<24)+(componentIndex<<16)+(component<<8); // 0x00iiccmm index,component, inputs
    }
    if (doDebugInfo==true){
       int pri=v->mcomp[v->currentc-1]>>24&0xff;
       printf("0x%08x ", v->mcomp[v->currentc-1]);
       if (pri==0) printf("       (");else printf(" pr[%d](",pri-1);
       printcomponent(v->mcomp[v->currentc-1]>>8&0xff);
       printf("[%d]) input[%d] ",v->mcomp[v->currentc-1]>>16&0xff,v->mcomp[v->currentc-1]&0xff);
       //if (v->mcomp[v->currentc-1]&0xff=vmMM) printf("pr[%d] ",v->mcomp[v->currentc-1]>>16&0xff);
       printf("\n" );
    }
}

//set context to component
int setcomponent(VM* v,int c,int i, U32 f){
    int a=0;
    switch (c) {
        case vmSMC: {
             v->smA[i].set(f,v->x.y);
             break;}
        case vmAPM1:{
             v->apm1A[i].cxt=(f);
             break;}
        case vmAPM2:{
             v->apm2A[i].cx=(f);
             break;}
        case vmTAPM:{
             v->tapmA[i].set(f, v->x.y);
             break;}
        case vmDS:{
             v->dsA[i].set(f,v->x.y);
             break;}
        case vmDHS:{
             a=v->dhsA[i].set(f,v->x.y);
             break;}
        case vmRCM:{
             v->rcmA[i].set(f,v->x.c4);
             break;}
        case vmSCM:{
             v->scmA[i].set(f);
             break;}
        case vmCM:{
             v->cmC[i]->set(f); 
             break;}
        case vmUAS:{
             v->uasA[i].set(f); 
             break;}
        case vmMX:{
             v->mxA[i].cxt=f;
             a=v->mxA[i].err>>3;
             break;}
        case vmST:{
            v->stA[i].set(f);
             break;}
        case vmMM: {
             break;}
        case vmSM:{
             v->smcA[i].set(f);
             break;}
        case vmSK:{
             v->skA[i].set(f);
             break;}
        case vmERR:{
             v->emA[i].cx=f;
             a=v->emA[i].q();
             break;}
        case vmBYT:{
             a=v->bmA[i].q();
             break;}
        case vmAVG:{ 
              v->avA[i].set(f);
             break;}
        case vmLMX:{ 
             break;}
        case vmSTA:{ 
             break;}
        default:{
             quit("VM vmx error\n");
             break;}
    }
    return a;
}
 
VM::VM(BlockData& bd):x(bd),prSize(0),mcomp(0),cmC(0),
vmstate(42,41,13,6,5,16,14)  //statable
//vmstate(20,48,15,8,6,5) //sz
{
    
    
    smc=apm1=apm2=tapm=uas=rcm=scm=cm=mx=st=av=mm=ds=dhs=sm=sk=statec=byt=currentc=totalc=initdone=mindex=totalPR=em=plpos=0;
    
    // init statetable
    for (int i=0;i<256;i++) vm_nn[0][i]=vmstate.next(i,0);
   for (int i=256;i<512;i++) vm_nn[0][i]=vmstate.next(i-256,1);
   for (int i=512;i<512+256;i++) vm_nn[0][i]=vmstate.next(i-512,2);
   for (int i=512+256;i<512+512;i++) vm_nn[0][i]=vmstate.next(i-256-512,3);
   for (int i=0;i<256;i++) {
            int n0=-!vmstate.next(i,2);
            int n1=-!vmstate.next(i,3);
            int r=0;
            if ((n1-n0)==1 ) r=2;
            if ((n1-n0)==-1 ) r=1;
            nn01[0][i]=r;
        }
    initdone=1;
}

VM::~VM() {killvm();
}

int vmbound(int line){
    if (line!=0)printf("Bounds error line: %d\n",line);
    exit(-1);
}

/*
int VM::getPrediction( ){
    int p;
    int prindex,index,compnr,mixnr;
        // mix inputs[0..x]
    if(x.cInputs>=0){     
        for (int j=0;j<x.cInputs+1;j++) {  
            for (int i=0;i< totalc;i++){
                int inputIndex=mcomp[i] &0xff ;    // index  
                int component=(mcomp[i]>>8)&0xff;
                if (j==inputIndex && (mcomp[i]>>24)==0 && (component==vmST|| component==vmSMC || component==vmRCM ||component==vmSCM || component==vmCM ||component==vmSM ||component==vmSK )) {

                    int componentIndex=mcomp[i]>>16;    // component index
                  //  printcomponent(component);printf("(%d).mix\n",componentIndex);
                    switch (component) { // select component and mix
                    case vmSMC: x.mxInputs[inputIndex].add(stretch(smA[componentIndex].pr));
                        break;
                    case vmRCM: rcmA[componentIndex].mix(x,inputIndex);
                        break;
                    case vmSCM: scmA[componentIndex].mix(x,inputIndex);
                        break;
                    case  vmCM: cmC[componentIndex]->mix(inputIndex);
                        break;
                    case  vmST: x.mxInputs[inputIndex].add(stA[componentIndex].pr);
                        break;
                    case vmSM: smcA[componentIndex].mix(x,inputIndex);
                        break;
                    case vmSK: skA[componentIndex].mix(x,inputIndex);
                        break;
                    case vmERR: 
                        break;
                    case vmBYT: 
                        break;
                    default:
                        quit("VM mxp error\n");
                        break;
                    }
                }
            }
        }
    }
 
    for (int i=0;i<totalc;i++){
        prindex=mcomp[i]>>24;
        index=(mcomp[i]>>16)&0xff;
        compnr=(mcomp[i]>>8)&0xff;
        mixnr=mcomp[i]&0xff;
        // individual components
        if ((prindex>0 || compnr==vmMM )){
          //if (compnr!=vmMM )printcomponent(compnr),printf("%d ",i);
         // printcomponent(compnr);printf("(%d)\n",index);
            prindex--;
            switch (compnr) {
            case vmSMC: {
                prSize[prindex]=smA[index].pr;
                break;
            }  
            case vmAPM1: {
                prSize[prindex]=apm1A[index].p(prSize[apm1A[index].p1],x.y);
                break;
            }
            case vmAPM2: {
                prSize[prindex]=apm2A[index].p(prSize[apm2A[index].p1],x.y);
                break;
            }
            case vmTAPM: {
                prSize[prindex]=tapmA[index].p(x.y);
                break;
            }
            case vmUAS: {
                prSize[prindex]=uasA[index].p(x.y);
                break;
            }
            case vmDS: {
                prSize[prindex]=dsA[index].p();
                break;
            }
             case vmDHS: {
                prSize[prindex]=dhsA[index].p();
                break;
            }
            case vmAVG: {
                prSize[prindex]=avA[index].average(&prSize[0]);
                break;
            }
            case vmLMX: {
                prSize[prindex]=lmxA[index].average(&prSize[0]);
                break;
            }
            case vmMM: {
                mmA[index].p=prSize[ mmA[index].i1];
                x.mxInputs[mixnr].add(mmA[index].pr());
                break; 
            }
            case vmMX: {
                prSize[prindex]=mxA[index].p();
                break;
            }
            case vmST: {
                 prSize[prindex]=stA[index].pr1;
                 break;
            }
            case vmSK: {
                 prSize[prindex]=skA[index].p();
                 break; 
            }
            default:{
                quit("VM vmi error\n");
                break;}
            }
            //if (compnr!=vmMM )printf("%d ",prSize[prindex-1]);
        }
        
    }  
   // if (compnr!=vmMM )
   //printf("  \n" );

    p=prSize[totalPR]; //final prediction
    return p;
}*/
/*
void VM::updateComponents(int p){
    int prindex,index,compnr;
    plpos=p;
    if(x.cInputs>=0){
        for (int i=0;i<totalc;i++){
            prindex=mcomp[i]>>24;
            compnr=(mcomp[i]>>8)&0xff;
            // individual components
            if (prindex>0 && compnr==vmMX){
                index=(mcomp[i]>>16)&0xff;
                //mxC[index]->update( mcomp[i]  &0xff); //update
                mxA[index].update(x.y);
            }
        }
        for (int j=0;j<x.cInputs+1;j++) {
            x.mxInputs[j].ncount=0; //reset
        }
    }
}
*/


