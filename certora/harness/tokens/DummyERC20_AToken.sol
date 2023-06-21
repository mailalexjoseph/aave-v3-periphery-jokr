// SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

import {IncentivizedERC20} from "@aave/core-v3/contracts/protocol/tokenization/base/IncentivizedERC20.sol";
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';

contract DummyERC20_AToken is IncentivizedERC20 {
    
      constructor(
    IPool pool,
    string memory name,
    string memory symbol,
    uint8 decimals
  ) IncentivizedERC20(pool, name, symbol, decimals) {
    // Intentionally left blank
  }

    function scaledTotalSupply() public view returns (uint256) {
        return super.totalSupply();
    }

    function scaledBalanceOf(address account) public view returns (uint256) {
        return super.balanceOf(account);
    }

    function getScaledUserBalanceAndSupply(address account) public view returns (uint256, uint256){
        return (scaledBalanceOf(account), scaledTotalSupply());
    }
}
