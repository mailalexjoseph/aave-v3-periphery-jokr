import "./ERC20_methods.spec";

using DummyERC20_AToken as AToken;

methods {
    // AToken functions
    function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
    function _.scaledTotalSupply() external => DISPATCHER(true);

    // TransferStrategyBase functions
    function _.performTransfer(address, address, uint256) external => DISPATCHER(true);

    // Oracle - assume any value 
    function _.latestAnswer() external => NONDET;

    //envfree functions
    function getUserAccruedRewards(address, address ) external returns(uint256) envfree; 
    function getClaimer(address) external returns (address) envfree;
}