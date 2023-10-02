import "methods/Methods_base.spec";


/*
Prove a basic property of an internal function so we know it is a safe assumption.
Here we don't have summarization

https://prover.certora.com/output/40726/2d29c7586ab34319a73ed926b0b99204/?anonymousKey=a3eb32605c8fd674bd6c0a5400e3b12e3c71c222



*/

methods {
    
    function computeNewIndexChange( uint256 totalSupply, uint256 block_timestamp, 
                                    uint256 lastUpdateTimestamp, uint256 distributionEnd, 
                                    uint256 emissionPerSecond, uint256 assetUnit ) external  returns(uint256) envfree;
            
}


/* check the original code  */
rule verifyMonotonicity( uint256 ts,  uint256 t1, uint256 t2, uint256 last, uint256 dis, uint256 ePerSec, uint256 units) {

    assert  (t1 < t2 && ts>0 ) => computeNewIndexChange(ts,t1,last,dis,ePerSec,units) <= computeNewIndexChange(ts,t2,last,dis,ePerSec,units) ;
} 