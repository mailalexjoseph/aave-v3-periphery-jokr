import "methods/Methods_base.spec";


/*
demonstrate  modular approach to verification in order to deal with timeouts :
    - understand where the complexity comes from (RewardsController_simplification.spec )
    - prove a property on the internal part of getAssetIndex (RewardsController_verifyModularAssumptions.spec)
    - summarize the internal function and just assume the property we proved 

    Now we got a violation of a rule that was timing out 
     https://prover.certora.com/output/40726/6f965c7ebf2d42b2bdf09b3e04bcf97b/?anonymousKey=8de6ba232961c721f1883c32c5169bb657c711f6 

     fixing the rule provides us with
     https://prover.certora.com/output/40726/f911bf362fc744079af32b5eaa45966f/?anonymousKey=7d4a672e75bdbd4c0500ef44deaf8d23745a47de 
     which time out  

     combining with some simplification provides us fast results 
     https://prover.certora.com/output/40726/6ed5382afc9246eebeb998565fcfb780/?anonymousKey=901db129503be2be58ccce58c3d7fac76074706e 

*/

methods {
    // summarize the internal 
    function computeNewIndexChange( uint256 totalSupply, uint256 block_timestamp, 
                                    uint256 lastUpdateTimestamp, uint256 distributionEnd, 
                                    uint256 emissionPerSecond, uint256 assetUnit ) internal  returns(uint256) => 
            symbolicIndexChange(totalSupply, block_timestamp, lastUpdateTimestamp, distributionEnd, emissionPerSecond);
    
    function computeNewIndexChange( uint256 totalSupply, uint256 block_timestamp, 
                                    uint256 lastUpdateTimestamp, uint256 distributionEnd, 
                                    uint256 emissionPerSecond, uint256 assetUnit ) external  returns(uint256) envfree;
            
}


//deterministic value
ghost symbolicIndexChange(uint256 /*totalSupply*/, 
                uint256 /*block_timestamp*/, 
                uint256 /*lastUpdateTimestamp*/, 
                uint256 /*distributionEnd*/,
                uint256 /*emissionPerSecond*/ ) returns uint256
    {
    axiom  
        // monotonicity on time 
        ( forall uint256 ts. forall uint256 t1. forall uint256 t2. forall uint256 last. forall uint256 dis. forall uint256 ePerSec. 
                t1 < t2 => symbolicIndexChange(ts,t1,last,dis,ePerSec) <= symbolicIndexChange(ts,t2,last,dis,ePerSec) );
        // zero for zero totalSupply
     axiom   ( forall uint256 t. forall uint256 last. forall uint256 dis. forall uint256 ePerSec. 
                symbolicIndexChange(0,t,last,dis,ePerSec) == 0); 

} 



///////////////// Properties ///////////////////////

rule monotonicityOverTime(address user, address reward) {
    
    env e1; 
    env e2;
    address[] assets;
    require (e1.block.timestamp < e2.block.timestamp);
    
    require getlastUpdateTimestamp(assets[0],reward) <= e1.block.timestamp;
    require getAssetDecimals(assets[0]) == 6; 
    require ( assets.length  == 1);
    assert getUserRewards(e1, assets, user, reward) <=  getUserRewards(e2, assets, user, reward);
}




//same rule but let's start with some simplification - the faster we get violations the better 

function simplify_start(env e, address asset, address reward) {
    require getAssetDecimals(asset) == 6; 
    require getlastUpdateTimestamp(asset,reward) == e.block.timestamp;
}
rule monotonicityOverTime_simpleStart(address user, address reward) {
    
    env e1; 
    env e2;
    address[] assets;
    require (e1.block.timestamp < e2.block.timestamp);
    require ( assets.length  <= 1);
    simplify_start(e1, assets[0], reward);
    
    assert getUserRewards(e1, assets, user, reward) <=  getUserRewards(e2, assets, user, reward);

}


