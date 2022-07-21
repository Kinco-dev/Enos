
pragma solidity ^0.8.15;
/**
 * SPDX-License-Identifier: Unlicensed
 *
 * Tokenomics:
 *  Max Supply: 100,000,000,000
 *  Decimals: 18
 *  Token Name: Enos
 *  Symbol: ENOS
 * 
 * 
 * Buy Tax 7% :            Sell Tax 12% :
 *  Liquidity        1%      Liquidity      2%
 *  Rewards          3%      Rewards        4%
 *  Marketing        3%      Marketing      6%
 *
 */
interface IERC20 {

    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return (msg.sender);
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; 
        return msg.data;
    }
}

abstract contract Ownable is Context {
    address private _owner;
    address private _previousOwner;
    uint256 private _lockTime;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor ()  {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

     /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    function getUnlockTime() public view returns (uint256) {
        return _lockTime;
    }

    //Locks the contract for owner for the amount of time provided (seconds)
    function lock(uint256 time) public virtual onlyOwner {
        _previousOwner = _owner;
        _owner = address(0);
        _lockTime = block.timestamp + time;
        emit OwnershipTransferred(_owner, address(0));
    }
    
    //Unlocks the contract for owner when _lockTime is exceeds
    function unlock() public virtual {
        require(_previousOwner == msg.sender, "You don't have permission to unlock");
        require(block.timestamp> _lockTime , "Contract is still locked");
        emit OwnershipTransferred(_owner, _previousOwner);
        _owner = _previousOwner;
    }

}

// pragma solidity >=0.5.0;

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}


// pragma solidity >=0.5.0;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

// pragma solidity >=0.6.2;

interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}



// pragma solidity >=0.6.2;

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}


contract Enos is Context, IERC20, Ownable {

    mapping (address => uint256) private _rOwned;
    mapping (address => uint256) private _tOwned;
    mapping (address => mapping (address => uint256)) private _allowances;

    mapping (address => bool) private _isExcludedFromFee;

    mapping (address => bool) private _isExcludedFromReward;

    mapping (address => bool) private _isExcludedFromMaxSellTransactionAmount;
    address[] private _excludedFromReward;
   
    uint256 private constant MAX = ~uint256(0);
    uint256 private _tTotal = 100_000_000_000* 10**18; // 100MM
    uint256 private _rTotal = (MAX - (MAX % _tTotal));

    address public liquidityWallet;
    address public marketingWallet = 0x464a9D3bA96eF075aBbB5B0118dF3c3EdB63c36d;

    uint256 private _tFeeTotal;

   string private _name = "Enos";
    string private _symbol = "ENOS";
    uint8 private _decimals = 18;

    address constant private  DEAD = 0x000000000000000000000000000000000000dEaD;
    
    uint8 public sellRewardFee = 4;
    uint8 public buyRewardFee = 3;
    
    uint8 public sellLiquidityFee = 2;
    uint8 public buyLiquidityFee = 1;

    uint8 public sellMarketingFee = 6;
    uint8 public buyMarketingFee = 3;

    uint8 totalSellFees;
    uint8 totalBuyFees;

    IUniswapV2Router02 public uniswapV2Router;
    address public uniswapV2Pair;
    
    bool private _inSwapAndLiquify;
    bool public swapAndLiquifyEnabled = true;
    
    uint256 public maxSellTransactionAmount = 500_000_000 *10**18; //500M => 0.5%
    uint256 public swapTokensAtAmount =  10_000_000* 10**18; //10M => 0.01%

    // timestamp for when the token can be traded freely on PancakeSwap
    uint256 public launchTimestamp = 1685570401; // Wed May 31 2023 22:00:01 GMT+0000
    // addresses that can make transfers before PancakeSwap listing
    mapping (address => bool) private _presaleAddresses;
    // all known liquidity pools 
    mapping (address => bool) public automatedMarketMakerPairs;
    
    event MinTokensBeforeSwapUpdated(uint256 minTokensBeforeSwap);
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );

    event UniswapV2RouterUpdated(address indexed newAddress, address indexed oldAddress);
    event UniswapV2PairUpdated(address indexed newAddress, address indexed oldAddress);
    event MarketingWalletUpdated(address indexed newMarketingWallet, address indexed oldMarketingWallet);
    event LiquidityWalletUpdated(address indexed newLiquidityWallet, address indexed oldLiquidityWallet);
    event MaxSellTransactionAmountUpdated(uint256 amount);

    event ExcludeFromFees(address indexed account);
    event ExcludeFromReward(address indexed account);
    event ExcludeFromMaxSellTransactionAmount(address indexed account);
    event IncludeInFees(address indexed account);
    event IncludeInReward(address indexed account);
    event IncludeInMaxSellTransactionAmount(address indexed account);

    event SellFeesUpdated(uint8 rewardFee,uint8 liquidityFee,uint8 marketingFee);
    event BuyFeesUpdated(uint8 rewardFee,uint8 liquidityFee,uint8 marketingFee);

    event Burn(uint256 amount);

    event SetAutomatedMarketMakerPair(address indexed pair, bool indexed value);

    event PresaleAddressAdded(address indexed presaleAddress);

    event AmountBeforeSwapUpdated(uint256 amount);



    modifier lockTheSwap {
        _inSwapAndLiquify = true;
        _;
        _inSwapAndLiquify = false;
    }

    struct tTransferValues { 
      uint256 tAmount;
      uint256 tTransferAmount;
      uint256 tRewardFee;
      uint256 tLiquidityFee;
      uint256 tMarketingFee;
   }

    struct rTransferValues { 
      uint256 rAmount;
      uint256 rTransferAmount;
      uint256 rRewardFee;
      uint256 rLiquidityFee;
      uint256 rMarketingFee;

   }

    constructor ()  {
        _rOwned[_msgSender()] = _rTotal;
        
        uniswapV2Router = IUniswapV2Router02(0x10ED43C718714eb63d5aA57B78B54704E256024E);
         // Create a uniswap pair for this new token with BNB
        uniswapV2Pair = IUniswapV2Factory(uniswapV2Router.factory())
            .createPair(address(this), uniswapV2Router.WETH());

        _setAutomatedMarketMakerPair(uniswapV2Pair, true);
      
        _isExcludedFromFee[owner()] = true;
        _isExcludedFromFee[address(this)] = true;
        _isExcludedFromFee[DEAD] = true;
        _isExcludedFromFee[marketingWallet] = true;

        totalBuyFees = buyLiquidityFee + buyMarketingFee + buyRewardFee;
        totalSellFees = sellLiquidityFee + sellMarketingFee + sellRewardFee;


        // exclude pair and other wallets from reward
        excludeFromReward(owner());
        excludeFromReward(address(this));
        excludeFromReward(DEAD);
        excludeFromReward(marketingWallet);

        _isExcludedFromMaxSellTransactionAmount[owner()] = true;
        _isExcludedFromMaxSellTransactionAmount[address(this)] = true;

        _presaleAddresses[owner()] = true;
        liquidityWallet = owner();


        emit Transfer(address(0), _msgSender(), _tTotal);
    }

    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public view returns (uint8) {
        return _decimals;
    }

    function totalSupply() public view override returns (uint256) {
        return _tTotal;
    }
    function balanceOf(address account) public view override returns (uint256) {
        if (_isExcludedFromReward[account]) return _tOwned[account];
        return tokenFromReflection(_rOwned[account]);
    }

    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()] - amount);
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender] + addedValue);
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender] - subtractedValue);
        return true;
    }

    function totalRewardFeesDistributed() public view returns (uint256) {
        return _tFeeTotal;
    }

    function setAutomatedMarketMakerPair(address pair, bool value) external onlyOwner {
        require(pair != uniswapV2Pair, "Enos: The PancakeSwap pair cannot be removed from automatedMarketMakerPairs");

        _setAutomatedMarketMakerPair(pair, value);
    }

    function _setAutomatedMarketMakerPair(address pair, bool value) private {
        require(automatedMarketMakerPairs[pair] != value, "Enos: Automated market maker pair is already set to that value");
        automatedMarketMakerPairs[pair] = value;

        if(value) {
            excludeFromReward(pair);
        }

        emit SetAutomatedMarketMakerPair(pair, value);
    }

    // Allows a wallet to distribute rewards
    function deliver(uint256 tAmount) external {
        address sender = _msgSender();
        require(!_isExcludedFromReward[sender], "Enos: Excluded addresses from reward cannot call this function");
        uint256 rAmount = reflectionFromToken(tAmount);
        _rOwned[sender] -= rAmount;
        _rTotal -= rAmount;
        _tFeeTotal += tAmount;
    }

    function reflectionFromToken(uint256 tAmount, bool deductTransferFee, bool isSellTransaction) public view returns(uint256) {
        require(tAmount <= _tTotal, "Enos: Amount must be less than supply");
        if (!deductTransferFee) {
            uint256 rAmount = reflectionFromToken(tAmount);
            return rAmount;
        } else {
            (, rTransferValues memory rValues) = _getValuesWithFees(tAmount,isSellTransaction);
            return rValues.rTransferAmount;
        }
    }

    function reflectionFromToken(uint256 tAmount) private view returns(uint256) {
        return tAmount * _getRate();
    }

    function tokenFromReflection(uint256 rAmount) public view returns(uint256) {
        require(rAmount <= _rTotal, "Enos: Amount must be less than total reflections");
        uint256 currentRate =  _getRate();
        return rAmount / currentRate;
    }

    function excludeFromReward(address account) public onlyOwner {
        require(!_isExcludedFromReward[account], "Enos: Account is already excluded from reward");
        require(_excludedFromReward.length <= 1000, "No more than 1000 addresses can be excluded from the rewards");
        if(_rOwned[account] > 0) {
            _tOwned[account] = tokenFromReflection(_rOwned[account]);
        }
        _isExcludedFromReward[account] = true;
        _excludedFromReward.push(account);
        emit ExcludeFromReward(account);
    }

    function includeInReward(address account) external onlyOwner {
        require(account != address(this) && account != marketingWallet, "Enos: This account cannot be included in reward");
        require(_isExcludedFromReward[account], "Enos: Account is already included in reward");
        for (uint256 i = 0; i < _excludedFromReward.length; i++) {
            if (_excludedFromReward[i] == account) {
                _excludedFromReward[i] = _excludedFromReward[_excludedFromReward.length - 1];
                _tOwned[account] = 0;
                _isExcludedFromReward[account] = false;
                _excludedFromReward.pop();
                break;
            }
        }
        emit IncludeInReward(account);
    }
    
    function excludeFromFees(address account) public onlyOwner {
        require(!_isExcludedFromFee[account], "Enos: Account is already excluded from fee");
        _isExcludedFromFee[account] = true;
        emit ExcludeFromFees(account);
    }

    function includeInFees(address account) public onlyOwner {
        require(_isExcludedFromFee[account], "Enos: Account is already included in fee");
        _isExcludedFromFee[account] = false;
        emit ExcludeFromFees(account);
    }

    function excludeFromMaxSellTransactionAmount(address account) public onlyOwner {
        require(!_isExcludedFromMaxSellTransactionAmount[account], "Enos: Account is already excluded from max transfer amount");
        _isExcludedFromMaxSellTransactionAmount[account] = true;
        emit ExcludeFromMaxSellTransactionAmount(account);
    }
    function includeInMaxSellTransactionAmount(address account) public onlyOwner {
        require(_isExcludedFromMaxSellTransactionAmount[account], "Enos: Account is already included in max transfer amount");
        _isExcludedFromMaxSellTransactionAmount[account] = false;
        emit IncludeInMaxSellTransactionAmount(account);
    }

    function addPresaleAddress(address newPresaleAddress) external onlyOwner {
        require(!_presaleAddresses[newPresaleAddress],"Enos: Address is already added");
        _presaleAddresses[newPresaleAddress] = true;
        emit PresaleAddressAdded(newPresaleAddress);
    }
    
    function setBuyFeePercents(uint8 rewardFee,uint8 liquidityFee,uint8 marketingFee) external onlyOwner {
        uint8 newTotalBuyFees = rewardFee + liquidityFee + marketingFee;
        require(newTotalBuyFees <=7 , "Enos: Total buy fees must be lower or equals to 7%");
        buyRewardFee = rewardFee;
        buyLiquidityFee = liquidityFee;
        buyMarketingFee = marketingFee;
        totalBuyFees = newTotalBuyFees;
        emit BuyFeesUpdated(rewardFee, liquidityFee, marketingFee);
    }
    
    function setSellFeePercents(uint8 rewardFee,uint8 liquidityFee,uint8 marketingFee) external onlyOwner {
        uint8 newTotalSellFees = rewardFee + liquidityFee + marketingFee;
        require(newTotalSellFees <=12 , "Enos: Total sell fees must be lower or equals to 12%");
        sellRewardFee = rewardFee;
        sellLiquidityFee = liquidityFee;
        sellMarketingFee = marketingFee;
        totalSellFees = newTotalSellFees;
        emit SellFeesUpdated(rewardFee, liquidityFee, marketingFee);
    }
   
    function setMaxSellTransactionAmount(uint256 amount) external onlyOwner {
        require(amount >= 100_000 && amount <= 10_000_000_000, "Enos: Amount must be between 100 000 and 10 000 000 000");
        require(maxSellTransactionAmount != amount *10**18, "Enos: maxSellTransactionAmount has already this value");
        maxSellTransactionAmount = amount *10**18;
        emit MaxSellTransactionAmountUpdated(maxSellTransactionAmount);
    }
    
    function setSwapTokenAtAmount(uint256 amount) external onlyOwner {
        require(amount >= 1 && amount <= 2_000_000_000, "Enos: Amount must be between 1 and 2 000 000 000");
        require(swapTokensAtAmount != amount *10**18, "Enos: swapTokenAtAmount has already this value");
        swapTokensAtAmount = amount *10**18;
        emit AmountBeforeSwapUpdated(amount);
    }

    
     //to recieve BNB from uniswapV2Router when swaping
    receive() external payable {
    }

    function _reflectFee(uint256 rRewardFee, uint256 tRewardFee) private {
        _rTotal -= rRewardFee;
        _tFeeTotal += tRewardFee;
    }


    function _getValuesWithFees(uint256 tAmount, bool isSellTransfer) private view returns (tTransferValues memory, rTransferValues memory) {
        tTransferValues memory tValues= _getTValues(tAmount,isSellTransfer);
        rTransferValues memory rValues= _getRValues(tValues);
        return (tValues,rValues);
    }

    function _getTValues(uint256 tAmount,bool isSellTransfer) private view returns (tTransferValues memory) {
        (uint256 tRewardFee, uint256 tLiquidityFee, uint256 tMarketingFee) = _calculateFees(tAmount, isSellTransfer);
        uint256 tTransferAmount = tAmount - tRewardFee - tLiquidityFee - tMarketingFee;
        return tTransferValues(tAmount,tTransferAmount, tRewardFee, tLiquidityFee, tMarketingFee);
    }

    function _getRValues(tTransferValues memory tValues) private view returns (rTransferValues memory) {
        uint256 currentRate = _getRate();
        uint256 rAmount = tValues.tAmount * currentRate;
        uint256 rRewardFee = tValues.tRewardFee * currentRate;
        uint256 rLiquidityFee = tValues.tLiquidityFee * currentRate;
        uint256 rMarketingFee = tValues.tMarketingFee * currentRate;
        uint256 rTransferAmount = rAmount - rRewardFee - rLiquidityFee - rMarketingFee;
        return rTransferValues(rAmount, rTransferAmount, rRewardFee, rLiquidityFee, rMarketingFee);
    }
    function _getRate() private view returns(uint256) {
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        return rSupply / tSupply;
    }

    function _getCurrentSupply() private view returns(uint256, uint256) {
        uint256 rSupply = _rTotal;
        uint256 tSupply = _tTotal;
        for (uint256 i = 0; i < _excludedFromReward.length; i++) {
            if (_rOwned[_excludedFromReward[i]] > rSupply || _tOwned[_excludedFromReward[i]] > tSupply) return (_rTotal, _tTotal);
            rSupply -= _rOwned[_excludedFromReward[i]];
            tSupply -= _tOwned[_excludedFromReward[i]];
        }
        if (rSupply < _rTotal / _tTotal) return (_rTotal, _tTotal);
        return (rSupply, tSupply);
    }

    function _calculateFees(uint256 amount, bool isSellTransaction) private view returns (uint256,uint256,uint256) {
        if(isSellTransaction) {
            return(amount*sellRewardFee/100,amount*sellLiquidityFee/100,amount*sellMarketingFee/100);
        }
        else {
            return(amount*buyRewardFee/100,amount*buyLiquidityFee/100,amount*buyMarketingFee/100);
        }
        
    }
    
    function isExcludedFromFee(address account) public view returns(bool) {
        return _isExcludedFromFee[account];
    }
    function isExcludedFromReward(address account) public view returns(bool) {
        return _isExcludedFromReward[account];
    }
    function isExcludedFromMaxSellTransactionAmount(address account) public view returns(bool) {
        return _isExcludedFromMaxSellTransactionAmount[account];
    }

    function _approve(address owner, address spender, uint256 amount) private {
        require(owner != address(0), "BEP20: approve from the zero address");
        require(spender != address(0), "BEP20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) private {
        require(from != address(0), "BEP20: transfer from the zero address");
        require(to != address(0), "BEP20: transfer to the zero address");
        require(amount >= 0, "BEP20: Transfer amount must be greater or equal to zero");

        bool isLaunched = isTokenLaunched();

        if(!isLaunched) {
            require(_presaleAddresses[from], "Enos: This account cannot send tokens before the launch");
        }
        bool isSellTransfer = automatedMarketMakerPairs[to];
        if( 
        	!_inSwapAndLiquify && isLaunched &&
            isSellTransfer && // sells only by detecting transfer to automated market maker pair
        	from != address(uniswapV2Router) && //router -> pair is removing liquidity which shouldn't have max
            !_isExcludedFromMaxSellTransactionAmount[to] && !_isExcludedFromMaxSellTransactionAmount[from] //no max for those excluded from max transaction amount
        ) {
            require(amount <= maxSellTransactionAmount, "Enos: Sell transfer amount exceeds the maxSellTransactionAmount.");
        }
      
		uint256 contractTokenBalance = balanceOf(address(this));
        
        bool canSwap = contractTokenBalance >= swapTokensAtAmount;
        
        if (
            canSwap &&
            !_inSwapAndLiquify&&
            !automatedMarketMakerPairs[from] && // not during buying
            from != liquidityWallet &&
            to != liquidityWallet
        ) {
            //add liquidity
            _swapAndLiquify();
        }
        
        bool isBuyTransfer = automatedMarketMakerPairs[from];
        bool takeFee = isLaunched && !_inSwapAndLiquify && (isBuyTransfer || isSellTransfer);

        // if any account belongs to _isExcludedFromFee account then remove the fee
        if(_isExcludedFromFee[from] || _isExcludedFromFee[to]) {
            takeFee = false;
        }
        
        _tokenTransfer(from,to,amount,takeFee,isSellTransfer);
    }

    function _swapAndLiquify() private lockTheSwap {
        uint256 totalTokens = balanceOf(address(this));
        uint256 liquidityTokensToNotSwap = totalTokens / 2;
        // initial BNB amount
        uint256 initialBalance = address(this).balance;
        // swap tokens for BNB
        _swapTokensForBNB(totalTokens - liquidityTokensToNotSwap);

        // how much ETH did we just swap into?
        uint256 newBalance = address(this).balance - initialBalance;
        // add liquidity to PancakeSwap
        _addLiquidity(liquidityTokensToNotSwap, newBalance);
        // send BNB to marketing wallet
        emit SwapAndLiquify(totalTokens - liquidityTokensToNotSwap, newBalance, liquidityTokensToNotSwap);
    }

    function _swapTokensForBNB(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniswapV2Router.WETH();

        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // make the swap
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    function _addLiquidity(uint256 tokenAmount, uint256 bnbAmount) private {
        // approve token transfer to cover all possible scenarios
        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // add the liquidity
        uniswapV2Router.addLiquidityETH{value: bnbAmount}(
            address(this),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            liquidityWallet, // send to liquidity wallet
            block.timestamp
        );
    }

    function _tokenTransfer(address sender, address recipient, uint256 amount,bool takeFee, bool isSellTransfer) private {
        tTransferValues memory tValues;
        rTransferValues memory rValues;

        if(!takeFee) {
            tValues = tTransferValues(amount, amount,0,0,0);
            uint256 rAmount = amount * _getRate();
            rValues = rTransferValues(rAmount, rAmount,0,0,0);
        }
        else {
        (tValues, rValues) = _getValuesWithFees(amount,isSellTransfer);
        }

        
        _rOwned[sender] -= rValues.rAmount;
        _rOwned[recipient] += rValues.rTransferAmount; 
        if (_isExcludedFromReward[recipient]) _tOwned[recipient] += tValues.tTransferAmount;
        if (_isExcludedFromReward[sender]) _tOwned[sender] -= tValues.tAmount;

        emit Transfer(sender, recipient, tValues.tTransferAmount);
        if(takeFee)
            _transferFees(tValues, rValues, sender);
    }

    function _transferFees(tTransferValues memory tValues, rTransferValues memory rValues, address sender) private {
        if(tValues.tLiquidityFee> 0) {
            _rOwned[address(this)] += rValues.rLiquidityFee;
            _tOwned[address(this)] += tValues.tLiquidityFee;
            emit Transfer(sender, address(this), tValues.tLiquidityFee);
        }
        if(tValues.tMarketingFee > 0) { 
            _rOwned[marketingWallet] += rValues.rMarketingFee;
            _tOwned[marketingWallet] += tValues.tMarketingFee;
            emit Transfer(sender, marketingWallet, tValues.tMarketingFee);
        }
        _reflectFee(rValues.rRewardFee, tValues.tRewardFee); // Distribute fees to holders

    }

    function batchTokensTransfer(address[] calldata addresses, uint256[] calldata amounts) external onlyOwner {
        require(addresses.length <= 200, "Enos: Batch transfer for maximum 200 addresses");
        require(addresses.length == amounts.length,"Enos: addresses and amounts must have the same length");
            for (uint i = 0; i < addresses.length; i++) {
                _transfer(_msgSender(),addresses[i],amounts[i]);
        }
    }

    function changeUniswapRouter(address newRouter) external onlyOwner {
        require(newRouter != address(uniswapV2Router), "Enos: The router has already that address");
        emit UniswapV2RouterUpdated(newRouter, address(uniswapV2Router));
        uniswapV2Router = IUniswapV2Router02(newRouter);      
    }

    function changeUniswapPair(address newPair) external onlyOwner {
        require(newPair != address(uniswapV2Pair), "Enos: The pair address has already that address");
        emit UniswapV2PairUpdated(newPair, address(uniswapV2Pair));
        uniswapV2Pair = newPair;
        excludeFromReward(uniswapV2Pair);
    }

    function getCirculatingSupply() external view returns (uint256) {
        return totalSupply() - balanceOf(DEAD) - balanceOf(address(0));
    }

    function burn(uint256 amount) external returns (bool) {
        _transfer(_msgSender(), DEAD, amount);
        emit Burn(amount);
        return true;
    }

    function sendLiquidityFeeManually() external onlyOwner {
        _swapAndLiquify();
    }

    function setMarketingWallet(address newWallet) external onlyOwner {
        require(newWallet != marketingWallet, "Enos: The marketing wallet has already that address");
        emit MarketingWalletUpdated(newWallet,marketingWallet);
         marketingWallet = newWallet;
        _isExcludedFromFee[newWallet] = true;
        excludeFromReward(newWallet);
    }

    function setLiquidityWallet(address newWallet) external onlyOwner {
        require(newWallet != liquidityWallet, "Enos: The liquidity wallet has already that address");
        emit LiquidityWalletUpdated(newWallet,liquidityWallet);
         liquidityWallet = newWallet;
    }

    function isTokenLaunched() public view returns (bool) {
        return block.timestamp >= launchTimestamp;
    }

    function setLaunchTimestamp(uint256 timestamp) external onlyOwner {
        require(launchTimestamp > block.timestamp, "Enos: Changing the timestamp is not allowed if the token is already launched");
        launchTimestamp = timestamp;
    }    

    function withdrawStuckBNBs(address payable to) external onlyOwner {
        require(address(this).balance > 0, "Enos: There are no BNBs in the contract");
        to.transfer(address(this).balance);
    }

    function withdrawStuckBEP20Tokens(address token, address to) external onlyOwner {
        require(token != address(this), "Enos: You are not allowed to get Enos tokens from the contract");
        require(IERC20(token).balanceOf(address(this)) > 0, "Enos: There are no tokens in the contract");
        IERC20(token).transfer(to, IERC20(token).balanceOf(address(this)));
    } 
}

// Made by @kinco_dev
