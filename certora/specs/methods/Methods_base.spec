import "./ERC20_methods.spec";

using DummyERC20_AToken as AToken;

methods {
    function getAssetRewardIndex(address, address) external returns (uint256) envfree;
    function getRewardsData(address, address) external returns (uint256, uint256, uint256, uint256) envfree;
    function getUserAssetIndex(address, address, address) external returns (uint256) envfree;
    
    function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
    function _.scaledTotalSupply() external => DISPATCHER(true);
    function _.performTransfer(address, address, uint256) external => DISPATCHER(true);
    function _.latestAnswer() external => NONDET;
}